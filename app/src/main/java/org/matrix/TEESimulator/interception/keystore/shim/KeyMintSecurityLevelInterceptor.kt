package org.matrix.TEESimulator.interception.keystore.shim

import android.hardware.security.keymint.Algorithm
import android.hardware.security.keymint.BlockMode
import android.hardware.security.keymint.Digest
import android.hardware.security.keymint.EcCurve
import android.hardware.security.keymint.KeyOrigin
import android.hardware.security.keymint.KeyParameter
import android.hardware.security.keymint.KeyParameterValue
import android.hardware.security.keymint.SecurityLevel
import android.hardware.security.keymint.Tag
import android.os.IBinder
import android.os.Parcel
import android.system.keystore2.*
import android.util.Pair as AndroidPair
import java.io.ByteArrayInputStream
import java.security.KeyFactory
import java.security.KeyPair
import java.security.SecureRandom
import java.security.cert.Certificate
import java.security.cert.CertificateFactory
import java.security.spec.PKCS8EncodedKeySpec
import java.util.Date
import java.util.concurrent.Callable
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ConcurrentLinkedDeque
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.locks.LockSupport
import org.matrix.TEESimulator.attestation.AttestationBuilder
import org.matrix.TEESimulator.attestation.AttestationConstants
import org.matrix.TEESimulator.attestation.AttestationPatcher
import org.matrix.TEESimulator.attestation.DeviceAttestationService
import org.matrix.TEESimulator.attestation.KeyMintAttestation
import org.matrix.TEESimulator.config.ConfigurationManager
import org.matrix.TEESimulator.interception.core.BinderInterceptor
import org.matrix.TEESimulator.interception.keystore.InterceptorUtils
import org.matrix.TEESimulator.interception.keystore.KeyIdentifier
import org.matrix.TEESimulator.interception.keystore.Keystore2Interceptor
import org.matrix.TEESimulator.logging.AttestationDossier
import org.matrix.TEESimulator.logging.SystemLogger
import org.matrix.TEESimulator.pki.CertGenConfig
import org.matrix.TEESimulator.pki.CertificateGenerator
import org.matrix.TEESimulator.pki.CertificateHelper
import org.matrix.TEESimulator.pki.KeyBoxManager
import org.matrix.TEESimulator.pki.NativeCertGen
import org.matrix.TEESimulator.util.AndroidDeviceUtils
import org.matrix.TEESimulator.util.AndroidPermissionUtils
import org.matrix.TEESimulator.util.TeeLatencySimulator

class KeyMintSecurityLevelInterceptor(
    private val original: IKeystoreSecurityLevel,
    private val securityLevel: Int,
) : BinderInterceptor() {

    data class GeneratedKeyInfo(
        val keyPair: KeyPair?,
        val secretKey: javax.crypto.SecretKey?,
        val nspace: Long,
        val response: KeyEntryResponse,
        val keyParams: KeyMintAttestation? = null,
    ) {
        /**
         * The USAGE_COUNT_LIMIT budget of this key instance. It lives with the instance, so a key
         * regenerated under the same alias starts afresh and an operation still holding the old
         * key never spends the new key's uses. Not persisted: a reboot restores the full budget.
         */
        val usage: UsageBudget? = keyParams?.usageCountLimit?.let { UsageBudget(it) }
    }

    /**
     * Uses not yet reserved by an operation, and uses spent by operations that finished. Only the
     * latter decides when the key is exhausted.
     */
    class UsageBudget(val limit: Int) {
        val remaining = java.util.concurrent.atomic.AtomicInteger(limit)
        val consumed = java.util.concurrent.atomic.AtomicInteger(0)
    }

    private val activeOps = ConcurrentHashMap<Int, ConcurrentLinkedDeque<SoftwareOperation>>()

    override fun onPreTransact(
        txId: Long,
        target: IBinder,
        code: Int,
        flags: Int,
        callingUid: Int,
        callingPid: Int,
        data: Parcel,
    ): TransactionResult {
        when (code) {
            GENERATE_KEY_TRANSACTION -> {
                logTransaction(txId, transactionNames[code]!!, callingUid, callingPid)

                return handleGenerateKey(txId, callingUid, callingPid, data)
            }
            CREATE_OPERATION_TRANSACTION -> {
                logTransaction(txId, transactionNames[code]!!, callingUid, callingPid)

                return handleCreateOperation(txId, callingUid, data)
            }
            IMPORT_KEY_TRANSACTION -> {
                logTransaction(txId, transactionNames[code]!!, callingUid, callingPid)

                data.enforceInterface(IKeystoreSecurityLevel.DESCRIPTOR)
                val keyDescriptor =
                    data.readTypedObject(KeyDescriptor.CREATOR)
                        ?: return TransactionResult.ContinueAndSkipPost
                if (keyDescriptor.domain != Domain.APP || keyDescriptor.alias == null)
                    return TransactionResult.ContinueAndSkipPost
                SystemLogger.info(
                    "[TX_ID: $txId] Forward to post-importKey hook for ${keyDescriptor.alias}[${keyDescriptor.nspace}]"
                )
                return TransactionResult.Continue
            }
            IMPORT_WRAPPED_KEY_TRANSACTION -> {
                logTransaction(txId, transactionNames[code]!!, callingUid, callingPid)

                data.enforceInterface(IKeystoreSecurityLevel.DESCRIPTOR)
                val keyDescriptor =
                    data.readTypedObject(KeyDescriptor.CREATOR)
                        ?: return TransactionResult.ContinueAndSkipPost
                if (keyDescriptor.domain != Domain.APP || keyDescriptor.alias == null)
                    return TransactionResult.ContinueAndSkipPost
                // Only the post hook's cleanup is needed, and only if something is cached.
                return if (hasCachedKey(KeyIdentifier(callingUid, keyDescriptor.alias)))
                    TransactionResult.Continue
                else TransactionResult.ContinueAndSkipPost
            }
        }

        logTransaction(
            txId,
            transactionNames[code] ?: "unknown code=$code",
            callingUid,
            callingPid,
            true,
        )

        return TransactionResult.ContinueAndSkipPost
    }

    override fun onPostTransact(
        txId: Long,
        target: IBinder,
        code: Int,
        flags: Int,
        callingUid: Int,
        callingPid: Int,
        data: Parcel,
        reply: Parcel?,
        resultCode: Int,
    ): TransactionResult {
        if (resultCode != 0 || reply == null || InterceptorUtils.hasException(reply))
            return TransactionResult.SkipTransaction

        if (code == IMPORT_WRAPPED_KEY_TRANSACTION) {
            data.enforceInterface(IKeystoreSecurityLevel.DESCRIPTOR)
            val keyDescriptor =
                data.readTypedObject(KeyDescriptor.CREATOR)
                    ?: return TransactionResult.SkipTransaction
            // The imported key replaced the alias in keystore2; what we cached for it is stale.
            cleanupKeyData(KeyIdentifier(callingUid, keyDescriptor.alias))
            return TransactionResult.SkipTransaction
        }

        if (code == IMPORT_KEY_TRANSACTION) {
            logTransaction(txId, "post-${transactionNames[code]!!}", callingUid, callingPid)

            data.enforceInterface(IKeystoreSecurityLevel.DESCRIPTOR)
            val keyDescriptor =
                data.readTypedObject(KeyDescriptor.CREATOR)
                    ?: return TransactionResult.SkipTransaction
            // A successful importKey replaces the alias's key in the real keystore2, so any prior
            // generate/patch cache for this alias is stale. Drop it: a non-attested import then
            // falls through to the real keystore2 (origin=IMPORTED, imported leaf), and the
            // attested-import branch below re-caches the fresh patched chain. Without this,
            // getKeyEntry replays the prior generated attestation (duck
            // STALE_GENERATED_AFTER_IMPORT).
            val keyId = KeyIdentifier(callingUid, keyDescriptor.alias)
            if (generatedKeys.remove(keyId) != null) {
                SystemLogger.debug("Remove generated key on importKey $keyId")
                // As in cleanupKeyData: a generation committed since owns the file.
                persist {
                    if (!generatedKeys.containsKey(keyId)) GeneratedKeyPersistence.delete(keyId)
                }
            }
            teeResponses.remove(keyId)
            patchedChains.remove(keyId)
            attestationKeys.remove(keyId)
            importedKeys.add(keyId)
            SystemLogger.trace {
                "[TRACE-$txId] post-importKey $keyId: added to importedKeys, skipUid=${ConfigurationManager.shouldSkipUid(callingUid)}"
            }

            if (!ConfigurationManager.shouldSkipUid(callingUid)) {
                val metadata: KeyMetadata =
                    reply.readTypedObject(KeyMetadata.CREATOR)
                        ?: return TransactionResult.SkipTransaction
                val originalChain = CertificateHelper.getCertificateChain(metadata)
                SystemLogger.trace {
                    "[TRACE-$txId] post-importKey $keyId: chainSize=${originalChain?.size ?: 0}"
                }
                if (originalChain != null && originalChain.size > 1) {
                    val newChain =
                        AttestationPatcher.patchCertificateChain(originalChain, callingUid)
                    CertificateHelper.updateCertificateChain(metadata, newChain).getOrThrow()
                    metadata.authorizations =
                        InterceptorUtils.patchAuthorizations(metadata.authorizations, callingUid)
                    patchedChains[keyId] = newChain
                    teeResponses[keyId] =
                        KeyEntryResponse().apply {
                            this.metadata = metadata
                            iSecurityLevel = original
                        }
                    SystemLogger.trace {
                        "[TRACE-$txId] post-importKey $keyId: PATCHED chain (chainSize=${newChain.size})"
                    }
                    SystemLogger.debug("Cached patched certificate chain for imported key $keyId.")
                    return InterceptorUtils.createTypedObjectReply(metadata)
                }
            }
        } else if (code == CREATE_OPERATION_TRANSACTION) {
            logTransaction(txId, "post-${transactionNames[code]!!}", callingUid, callingPid)

            data.enforceInterface(IKeystoreSecurityLevel.DESCRIPTOR)
            val keyDescriptor =
                data.readTypedObject(KeyDescriptor.CREATOR)
                    ?: return TransactionResult.SkipTransaction
            val params =
                data.createTypedArray(KeyParameter.CREATOR)
                    ?: return TransactionResult.SkipTransaction
            val parsedParams = KeyMintAttestation(params)
            val forced = data.readBoolean()
            if (forced)
                SystemLogger.verbose(
                    "[TX_ID: $txId] Current operation has a very high pruning power."
                )
            val response: CreateOperationResponse =
                reply.readTypedObject(CreateOperationResponse.CREATOR)
                    ?: return TransactionResult.SkipTransaction
            SystemLogger.verbose(
                "[TX_ID: $txId] CreateOperationResponse: ${response.iOperation} ${response.operationChallenge}"
            )

            // Intercept the IKeystoreOperation binder
            response.iOperation?.let { operation ->
                val operationBinder = operation.asBinder()
                if (!interceptedOperations.containsKey(operationBinder)) {
                    SystemLogger.info("Found new IKeystoreOperation. Registering interceptor...")
                    val backdoor = getBackdoor(target)
                    if (backdoor != null) {
                        val isAead = parsedParams.blockMode.firstOrNull() == BlockMode.GCM
                        val interceptor = OperationInterceptor(operation, backdoor, isAead)
                        register(
                            backdoor,
                            operationBinder,
                            interceptor,
                            OperationInterceptor.INTERCEPTED_CODES,
                        )
                        interceptedOperations[operationBinder] = interceptor
                    } else {
                        SystemLogger.error(
                            "Failed to get backdoor to register OperationInterceptor."
                        )
                    }
                }
            }
        } else if (code == GENERATE_KEY_TRANSACTION) {
            logTransaction(txId, "post-${transactionNames[code]!!}", callingUid, callingPid)

            val metadata: KeyMetadata =
                reply.readTypedObject(KeyMetadata.CREATOR)
                    ?: return TransactionResult.SkipTransaction

            data.enforceInterface(IKeystoreSecurityLevel.DESCRIPTOR)
            val keyDescriptor =
                data.readTypedObject(KeyDescriptor.CREATOR)
                    ?: return TransactionResult.SkipTransaction
            val keyId = KeyIdentifier(callingUid, keyDescriptor.alias)
            // The HAL generated the new key: only now drop what a prior generation cached for
            // this alias (handleGenerateKey defers it), before any early return below.
            cleanupKeyData(keyId)
            // An un-targeted app only came here to have its stale cache dropped: its real key is
            // served untouched.
            if (ConfigurationManager.shouldSkipUid(callingUid)) return TransactionResult.SkipTransaction

            val originalChain = CertificateHelper.getCertificateChain(metadata)
            if (originalChain == null || originalChain.size <= 1) {
                // Cache non-attested responses for KEY_ID getKeyEntry parity.
                // Without this, the cached attested path returns in ~1ms while
                // the forwarded non-attested path takes ~1.5ms, and
                // TimingSideChannelProbe flags the 1.55x ratio.
                cleanupKeyData(keyId)
                teeResponses[keyId] =
                    KeyEntryResponse().apply {
                        this.metadata = metadata
                        iSecurityLevel = original
                    }
                return TransactionResult.SkipTransaction
            }

            data.readTypedObject(KeyDescriptor.CREATOR) // skip attestationKey
            val keyParams = data.createTypedArray(KeyParameter.CREATOR)
            val certNotBefore =
                keyParams
                    ?.find { it.tag == Tag.CERTIFICATE_NOT_BEFORE }
                    ?.value
                    ?.dateTime
                    ?.let { Date(it) }
            val certNotAfter =
                keyParams
                    ?.find { it.tag == Tag.CERTIFICATE_NOT_AFTER }
                    ?.value
                    ?.dateTime
                    ?.let { Date(it) }

            val newChain =
                AttestationPatcher.patchCertificateChain(
                    originalChain,
                    callingUid,
                    certNotBefore,
                    certNotAfter,
                )

            val key = metadata.key ?: return TransactionResult.SkipTransaction
            CertificateHelper.updateCertificateChain(metadata, newChain).getOrThrow()
            metadata.authorizations =
                InterceptorUtils.patchAuthorizations(metadata.authorizations, callingUid)

            // PATCH decode point: the chain we rewrote onto a real TEE generateKey reply.
            AttestationDossier.log(callingUid, txId, "PATCH", newChain.asList())

            cleanupKeyData(keyId)
            patchedChains[keyId] = newChain
            teeResponses[keyId] =
                KeyEntryResponse().apply {
                    this.metadata = metadata
                    iSecurityLevel = original
                }
            SystemLogger.debug(
                "Cached patched certificate chain for $keyId. (${key.alias} [${key.domain}, ${key.nspace}])"
            )

            return InterceptorUtils.createTypedObjectReply(metadata)
        }
        return TransactionResult.SkipTransaction
    }

    private fun pruneOpsForUid(
        uid: Int,
        newOp: SoftwareOperation,
        maxOps: Int = MAX_CONCURRENT_OPS_PER_UID,
    ) {
        val ops = activeOps.computeIfAbsent(uid) { ConcurrentLinkedDeque() }
        val before = ops.size
        ops.removeIf { it.finalized }
        val afterClean = ops.size
        while (ops.size >= maxOps) {
            val oldest = ops.pollFirst() ?: break
            if (!oldest.finalized) {
                SystemLogger.info(
                    "[LRU] Pruning operation for uid=$uid (active=${ops.size}/$maxOps)"
                )
                // It may have ended in the meantime, which abort reports as an invalid handle.
                runCatching { oldest.abort() }
            }
        }
        ops.addLast(newOp)
        SystemLogger.debug(
            "[LRU] uid=$uid ops: before=$before cleaned=${before - afterClean} active=${ops.size}"
        )
    }

    private fun handleCreateOperation(
        txId: Long,
        callingUid: Int,
        data: Parcel,
    ): TransactionResult =
        runCatching {
                SystemLogger.debug(
                    "[TX_ID: $txId] createOperation parcel: dataSize=${data.dataSize()} dataAvail=${data.dataAvail()} dataPos=${data.dataPosition()}"
                )
                data.enforceInterface(IKeystoreSecurityLevel.DESCRIPTOR)
                val keyDescriptor = data.readTypedObject(KeyDescriptor.CREATOR)!!

                SystemLogger.debug(
                    "[TX_ID: $txId] createOperation descriptor: domain=${keyDescriptor.domain} nspace=${keyDescriptor.nspace} alias=${keyDescriptor.alias}"
                )

                // Android framework calls createOperation with domain=APP+alias;
                // keystore2 internally resolves to KEY_ID — but software keys never
                // reach keystore2's database, so we must handle both lookup paths.
                val resolvedEntry: Map.Entry<KeyIdentifier, GeneratedKeyInfo> =
                    when (keyDescriptor.domain) {
                        Domain.APP -> {
                            val alias =
                                keyDescriptor.alias
                                    ?: run {
                                        SystemLogger.info(
                                            "[TX_ID: $txId] createOperation domain=APP with null alias, forwarding to HAL"
                                        )
                                        return TransactionResult.ContinueAndSkipPost
                                    }
                            val key = KeyIdentifier(callingUid, alias)
                            generatedKeys[key]?.let { java.util.AbstractMap.SimpleEntry(key, it) }
                                ?: run {
                                    SystemLogger.info(
                                        "[TX_ID: $txId] createOperation alias=$alias not in generatedKeys, forwarding to HAL"
                                    )
                                    return TransactionResult.ContinueAndSkipPost
                                }
                        }
                        Domain.KEY_ID -> {
                            val nspace = keyDescriptor.nspace
                            val entry =
                                if (nspace == null || nspace == 0L) null
                                else
                                    generatedKeys.entries
                                        .filter { it.key.uid == callingUid }
                                        .find { it.value.nspace == nspace }
                            // Real-HAL operations are left to keystore2 and the HAL, which manage
                            // their own slots (keystore2 prunes and retries on TOO_MANY_OPERATIONS).
                            entry
                                // A grantee loads a granted key through Domain.GRANT and then
                                // operates on the KEY_ID the owner's metadata names, which is not
                                // under the grantee's uid.
                                ?: findGrantedKeyByKeyId(callingUid, nspace)?.let { (grant, info) ->
                                    if ((grant.accessVector and KEY_PERMISSION_USE) == 0) {
                                        return InterceptorUtils.createServiceSpecificErrorReply(
                                            RESPONSE_PERMISSION_DENIED
                                        )
                                    }
                                    java.util.AbstractMap.SimpleEntry(grant.ownerKeyId, info)
                                }
                                ?: run {
                                    SystemLogger.info(
                                        "[TX_ID: $txId] createOperation KeyId(${keyDescriptor.nspace}) NOT FOUND for uid=$callingUid. Forwarding to HAL."
                                    )
                                    return TransactionResult.ContinueAndSkipPost
                                }
                        }
                        Domain.GRANT -> {
                            // A grant we issued (Android 16 grantKeyAccess) names a software key
                            // keystore2 has never seen; the grantee uses it here, as the owner.
                            val grant =
                                resolveGrant(keyDescriptor.nspace, callingUid)
                                    ?: return if (softwareGrants.containsKey(keyDescriptor.nspace))
                                        InterceptorUtils.createServiceSpecificErrorReply(
                                            RESPONSE_KEY_NOT_FOUND
                                        )
                                    else TransactionResult.ContinueAndSkipPost
                            if ((grant.accessVector and KEY_PERMISSION_USE) == 0) {
                                return InterceptorUtils.createServiceSpecificErrorReply(
                                    RESPONSE_PERMISSION_DENIED
                                )
                            }
                            generatedKeys[grant.ownerKeyId]?.let {
                                java.util.AbstractMap.SimpleEntry(grant.ownerKeyId, it)
                            } ?: return TransactionResult.ContinueAndSkipPost
                        }
                        else -> {
                            SystemLogger.info(
                                "[TX_ID: $txId] createOperation domain=${keyDescriptor.domain}, forwarding to HAL"
                            )
                            return TransactionResult.ContinueAndSkipPost
                        }
                    }
                val generatedKeyInfo = resolvedEntry.value
                val resolvedKeyId = resolvedEntry.key

                // Software operations are bounded by pruneOpsForUid below: like keystore2, the
                // oldest live operation is aborted to make room instead of failing the new one.
                SystemLogger.info("[TX_ID: $txId] Creating SOFTWARE operation for uid=$callingUid.")

                val params = data.createTypedArray(KeyParameter.CREATOR)!!
                val parsedParams =
                    KeyMintAttestation(params).let { p ->
                        if (p.algorithm != 0) p
                        else {
                            val keyAlgo = generatedKeyInfo.keyPair?.private?.algorithm
                            p.copy(
                                algorithm =
                                    when (keyAlgo) {
                                        "EC",
                                        "ECDSA" -> Algorithm.EC
                                        "RSA" -> Algorithm.RSA
                                        else -> generatedKeyInfo.keyParams?.algorithm ?: p.algorithm
                                    }
                            )
                        }
                    }
                val forced = data.readBoolean()

                val requestedPurpose = parsedParams.purpose.firstOrNull()
                if (requestedPurpose == null) {
                    return InterceptorUtils.createServiceSpecificErrorReply(
                        KEYMINT_INVALID_ARGUMENT
                    )
                }

                if (forced) {
                    return InterceptorUtils.createServiceSpecificErrorReply(
                        RESPONSE_PERMISSION_DENIED
                    )
                }

                AuthorizeCreate.check(generatedKeyInfo.keyParams, parsedParams, params)?.let {
                    errorCode ->
                    SystemLogger.info(
                        "[TX_ID: $txId] authorize_create rejected: errorCode=$errorCode"
                    )
                    return InterceptorUtils.createServiceSpecificErrorReply(errorCode)
                }

                val keyParams = generatedKeyInfo.keyParams
                val effectiveParams =
                    if (keyParams != null) {
                        keyParams.copy(
                            purpose = parsedParams.purpose,
                            digest = parsedParams.digest.ifEmpty { keyParams.digest },
                            blockMode = parsedParams.blockMode.ifEmpty { keyParams.blockMode },
                            padding = parsedParams.padding.ifEmpty { keyParams.padding },
                            rsaOaepMgfDigest =
                                parsedParams.rsaOaepMgfDigest.ifEmpty {
                                    keyParams.rsaOaepMgfDigest
                                },
                            nonce = parsedParams.nonce,
                            // A key property: an operation may not lower the floor it verifies
                            // MACs against.
                            minMacLength = keyParams.minMacLength,
                            macLength = parsedParams.macLength,
                        )
                    } else parsedParams

                val opLatency =
                    when (securityLevel) {
                        SecurityLevel.STRONGBOX -> STRONGBOX_OP_LATENCY_FLOOR_MS
                        SecurityLevel.TRUSTED_ENVIRONMENT -> TEE_OP_LATENCY_FLOOR_MS
                        else -> 0L
                    }
                val softwareOperation =
                    SoftwareOperation(
                        txId,
                        generatedKeyInfo.keyPair,
                        generatedKeyInfo.secretKey,
                        effectiveParams,
                        opLatency,
                    )

                val usage = generatedKeyInfo.usage
                if (usage != null) {
                    val limit = usage.limit
                    // A use is reserved up front, so concurrent operations cannot overrun the
                    // limit; an operation that does not finish gives its use back. A failed
                    // reservation only means the uses are taken by operations still in flight,
                    // any of which may yet give its use back, so the key stays.
                    val reserved =
                        usage.remaining.getAndUpdate { if (it > 0) it - 1 else it } > 0
                    if (!reserved) {
                        return InterceptorUtils.createServiceSpecificErrorReply(
                            RESPONSE_KEY_NOT_FOUND
                        )
                    }
                    softwareOperation.onEnd = { success ->
                        if (!success) {
                            usage.remaining.incrementAndGet()
                        } else if (usage.consumed.incrementAndGet() >= limit) {
                            // Found and dropped on the persistence thread, where alias
                            // replacements and migrations are committed: only the key this
                            // operation was created for goes, never a newer key generated under
                            // the alias, and it is found by identity wherever a migration put it.
                            persist {
                                generatedKeys.entries
                                    .firstOrNull { it.value === generatedKeyInfo }
                                    ?.key
                                    ?.let { cleanupKeyData(it) }
                            }
                            SystemLogger.info(
                                "Key $resolvedKeyId exhausted (USAGE_COUNT_LIMIT=$limit)."
                            )
                        }
                    }
                }

                val maxOps =
                    if (securityLevel == SecurityLevel.STRONGBOX) STRONGBOX_MAX_CONCURRENT_OPS
                    else MAX_CONCURRENT_OPS_PER_UID
                pruneOpsForUid(callingUid, softwareOperation, maxOps)
                val operationBinder = SoftwareOperationBinder(softwareOperation)

                val response =
                    CreateOperationResponse().apply {
                        iOperation = operationBinder
                        operationChallenge = null
                        parameters = softwareOperation.beginParameters
                    }

                InterceptorUtils.createTypedObjectReply(response)
            }
            .getOrElse {
                SystemLogger.error("Error during createOperation for UID $callingUid.", it)
                InterceptorUtils.createServiceSpecificErrorReply(KEYMINT_UNKNOWN_ERROR)
            }

    private fun handleGenerateKey(
        txId: Long,
        callingUid: Int,
        callingPid: Int,
        data: Parcel,
    ): TransactionResult {
        if (SystemLogger.isUidLogged(callingUid)) {
            val savedPos = data.dataPosition()
            val req = data.marshall()
            data.setDataPosition(savedPos)
            SystemLogger.uidLogRaw(callingUid, txId, "genkey-request", "len=${req.size}", req)
        }
        val oversized = data.dataSize() > MAX_ALIAS_LENGTH

        return runCatching {
                data.enforceInterface(IKeystoreSecurityLevel.DESCRIPTOR)
                val keyDescriptor = data.readTypedObject(KeyDescriptor.CREATOR)!!
                // Software keys are cached per app alias; a key in another domain (SELINUX
                // namespaces, BLOB) is not the caller's to shadow.
                if (keyDescriptor.domain != Domain.APP || keyDescriptor.alias == null)
                    return TransactionResult.ContinueAndSkipPost
                val attestationKey = data.readTypedObject(KeyDescriptor.CREATOR)

                SystemLogger.debug(
                    "Handling generateKey ${keyDescriptor.alias}, attestKey=${attestationKey?.alias}"
                )
                // INCLUDE_UNIQUE_ID requires SELinux gen_unique_id OR
                // REQUEST_UNIQUE_ID_ATTESTATION (AOSP security_level.rs:478-485). AOSP
                // rejects with PERMISSION_DENIED when neither is held, but that breaks
                // Google Wallet card binding and regresses Play Integrity: Wallet's
                // generateKey carries the tag without the permission. Strip it at parse
                // so the key generates and the attestation omits unique_id (pre-PR157
                // behavior). Deciding here keeps params/parsedParams val and derives
                // isAttestKeyRequest from the effective parameters.
                val params =
                    data.createTypedArray(KeyParameter.CREATOR)!!.let { raw ->
                        val stripUniqueId =
                            raw.any { it.tag == Tag.INCLUDE_UNIQUE_ID } &&
                                !ConfigurationManager.checkSELinuxPermission(
                                    callingPid,
                                    "keystore_key",
                                    "gen_unique_id",
                                ) &&
                                !ConfigurationManager.hasPermissionForUid(
                                    callingUid,
                                    "android.permission.REQUEST_UNIQUE_ID_ATTESTATION",
                                )
                        if (stripUniqueId) {
                            SystemLogger.debug(
                                "[TX_ID: $txId] Stripping INCLUDE_UNIQUE_ID for uid=$callingUid pid=$callingPid (no permission)"
                            )
                            raw.filter { it.tag != Tag.INCLUDE_UNIQUE_ID }.toTypedArray()
                        } else raw
                    }
                val parsedParams = KeyMintAttestation(params)
                val isAttestKeyRequest = parsedParams.isAttestKey()

                val hasDeviceIdAttestation =
                    params.any {
                        it.tag == Tag.ATTESTATION_ID_IMEI ||
                            it.tag == Tag.ATTESTATION_ID_MEID ||
                            it.tag == Tag.ATTESTATION_ID_SERIAL ||
                            it.tag == Tag.DEVICE_UNIQUE_ATTESTATION ||
                            it.tag == Tag.ATTESTATION_ID_SECOND_IMEI
                    }

                // One `dispatch` record per generateKey on the targeted UID's diagnostic plane,
                // carrying the resolved outcome and the request shape that drove it. Scoped to
                // targeted UIDs, so the SKIP flood from every other app never reaches the plane;
                // release builds short-circuit before any string is built.
                fun logProbe(outcome: String) {
                    if (!SystemLogger.isUidLogged(callingUid)) return
                    val tags =
                        buildList {
                                if (parsedParams.attestationChallenge != null) add("challenge")
                                if (
                                    parsedParams.brand != null ||
                                        parsedParams.device != null ||
                                        parsedParams.product != null ||
                                        parsedParams.manufacturer != null ||
                                        parsedParams.model != null
                                )
                                    add("props")
                                if (hasDeviceIdAttestation) add("ids")
                                if (params.any { it.tag == Tag.INCLUDE_UNIQUE_ID }) add("unique_id")
                            }
                            .joinToString(",")
                    SystemLogger.uidLog(
                        callingUid,
                        txId,
                        "dispatch",
                        "outcome=$outcome alias=${keyDescriptor.alias} " +
                            "algo=${parsedParams.algorithm} sb=${securityLevel == SecurityLevel.STRONGBOX} " +
                            "tags=[$tags]",
                    )
                }

                // Device-ID attestation (IMEI/MEID/serial) is a factory-provisioned capability the
                // real TEE frequently cannot satisfy (it returns CANNOT_ATTEST_IDS). A privileged
                // caller — shell/system, e.g. the Key Attestation app via Shizuku — is entitled to
                // request it, but arrives un-targeted, so don't skip it: it must reach the forge
                // path below. The permission gate still rejects ordinary apps further down.
                if (
                    ConfigurationManager.shouldSkipUid(callingUid) &&
                        attestationKey == null &&
                        !isAttestKeyRequest &&
                        !hasDeviceIdAttestation
                ) {
                    logProbe("SKIP")
                    // An app taken out of the target list may still have this alias cached from
                    // when it was targeted. Let the post hook drop that once the HAL has made the
                    // new key, or every later read and operation would keep using the old one.
                    return if (hasCachedKey(KeyIdentifier(callingUid, keyDescriptor.alias)))
                        TransactionResult.Continue
                    else TransactionResult.ContinueAndSkipPost
                }

                SystemLogger.trace {
                    "[TRACE-$txId] generateKey alias=${keyDescriptor.alias} algo=${parsedParams.algorithm} challenge=${parsedParams.attestationChallenge?.size ?: "null"} serial=${parsedParams.serial != null} imei=${parsedParams.imei != null} noAuth=${parsedParams.noAuthRequired} purposes=${parsedParams.purpose}"
                }
                if (SystemLogger.isDebugBuild)
                    params.forEach { p ->
                        SystemLogger.trace { "[TRACE-$txId] tag=${p.tag} value=${p.value}" }
                    }

                val challenge = parsedParams.attestationChallenge
                if (
                    challenge != null &&
                        challenge.size > AttestationConstants.CHALLENGE_LENGTH_LIMIT
                ) {
                    SystemLogger.warning(
                        "[TX_ID: $txId] Rejecting oversized attestation challenge: ${challenge.size} bytes (max ${AttestationConstants.CHALLENGE_LENGTH_LIMIT})"
                    )
                    logProbe("REJECT:challenge_len")
                    return InterceptorUtils.createErrorReply(KEYMINT_INVALID_INPUT_LENGTH)
                }

                if (params.any { it.tag == Tag.CREATION_DATETIME }) {
                    SystemLogger.warning(
                        "[TX_ID: $txId] Rejecting CREATION_DATETIME in generateKey params"
                    )
                    logProbe("REJECT:creation_datetime")
                    return InterceptorUtils.createErrorReply(RESPONSE_INVALID_ARGUMENT)
                }

                if (
                    params.any { it.tag == Tag.DEVICE_UNIQUE_ATTESTATION } &&
                        !AndroidPermissionUtils.hasUniqueIdAttestationPermission(callingUid)
                ) {
                    SystemLogger.warning(
                        "[TX_ID: $txId] Rejecting DEVICE_UNIQUE_ATTESTATION for uid=$callingUid"
                    )
                    logProbe("REJECT:cannot_attest_unique")
                    return InterceptorUtils.createErrorReply(KEYMINT_CANNOT_ATTEST_IDS)
                }

                // Device-ID attestation mirrors a real KeyMint: privileged callers (GMS/system)
                // get it, ordinary apps get CANNOT_ATTEST_IDS. The permission check below is that
                // rule. Device-property attestation (BRAND/MODEL/...) is honored unconditionally —
                // genuine devices universally attest it, and it is what Play Integrity's hardware
                // path needs. Capability is keyed to the device we present, not the real (dead)
                // TEE.
                if (
                    hasDeviceIdAttestation &&
                        !AndroidPermissionUtils.hasDeviceAttestationPermission(callingUid)
                ) {
                    SystemLogger.warning(
                        "[TX_ID: $txId] Rejecting DEVICE_ID_ATTESTATION for uid=$callingUid"
                    )
                    logProbe("REJECT:cannot_attest_ids")
                    return InterceptorUtils.createErrorReply(KEYMINT_CANNOT_ATTEST_IDS)
                }

                val isSymmetric =
                    parsedParams.algorithm == Algorithm.AES ||
                        parsedParams.algorithm == Algorithm.HMAC ||
                        parsedParams.algorithm == Algorithm.TRIPLE_DES

                if (securityLevel == SecurityLevel.STRONGBOX && !isStrongBoxCapable(parsedParams)) {
                    SystemLogger.info(
                        "[TX_ID: $txId] StrongBox-unsupported params (algo=${parsedParams.algorithm} size=${parsedParams.keySize}) → forwarding to HAL for rejection"
                    )
                    logProbe("FORWARD_HAL")
                    return TransactionResult.ContinueAndSkipPost
                }

                val keyId = KeyIdentifier(callingUid, keyDescriptor.alias)

                // keystore2 generateKey replaces an existing alias, so a prior generation's cache
                // must go or getKeyEntry serves a stale FORGE. But only once the new key exists:
                // doSoftwareKeyGen clears it itself, and a forwarded request is cleared by the
                // post-generateKey hook on success. Clearing up front would destroy the user's
                // existing key whenever the HAL then rejects the request.

                // Device-ID attestation must be forged, not patched: the real TEE returns
                // CANNOT_ATTEST_IDS, so there is no real chain to patch — only a synthetic one
                // carrying the requested IDs and rooted under the keybox will satisfy the caller.
                // AUTO forges asymmetric attestation only when the real hardware cannot provision an
                // attestation key for that algorithm at the requested security level: a device may
                // attest RSA in the TEE yet not in StrongBox, so the probe must match the request.
                // Devices that can attest keep their genuine chain via PATCH, which strict callers
                // accept where a forgery is rejected.
                val strongBox = securityLevel == SecurityLevel.STRONGBOX
                // Symmetric keys carry no certificate chain, so there is nothing to attest or
                // spoof. With a working TEE they go to the real HAL even in generate mode: a
                // software AES/HMAC key only adds risk (wrong authorizations made
                // react-native-keychain delete and regenerate its key forever, and any data it
                // encrypted dies with the module's key store). Only a dead TEE still needs them
                // forged.
                val forgeSymmetric = !DeviceAttestationService.isTeeFunctional
                // Neither forger handles Ed25519/X25519, so those keys always come from the HAL;
                // a chain it attests is patched like any other.
                val isCurve25519 =
                    parsedParams.algorithm == Algorithm.EC &&
                        parsedParams.ecCurve == EcCurve.CURVE_25519
                val forceGenerate =
                    !isCurve25519 && (oversized ||
                        (ConfigurationManager.shouldGenerate(callingUid) &&
                            (!isSymmetric || forgeSymmetric)) ||
                        isAttestKeyRequest ||
                        attestationKey != null ||
                        hasDeviceIdAttestation ||
                        (ConfigurationManager.isAutoMode(callingUid) &&
                            parsedParams.attestationChallenge != null &&
                            when (parsedParams.algorithm) {
                                Algorithm.RSA ->
                                    !DeviceAttestationService.isRsaAttestable(strongBox)
                                Algorithm.EC -> !DeviceAttestationService.isEcAttestable(strongBox)
                                else -> false
                            }))

                // An even public exponent has no inverse, and RSA key generation would search for
                // a key forever, holding a binder thread of every caller that tries.
                val exponent = parsedParams.rsaPublicExponent
                if (
                    forceGenerate &&
                        parsedParams.algorithm == Algorithm.RSA &&
                        exponent != null &&
                        (exponent <= java.math.BigInteger.ONE || !exponent.testBit(0))
                ) {
                    logProbe("REJECT:rsa_exponent")
                    return InterceptorUtils.createServiceSpecificErrorReply(KEYMINT_INVALID_ARGUMENT)
                }

                SystemLogger.trace {
                    "[TRACE-$txId] dispatch: forceGen=$forceGenerate hasChallenge=${challenge != null} isSymmetric=$isSymmetric isAttestKey=$isAttestKeyRequest"
                }

                when {
                    forceGenerate -> {
                        logProbe("FORGE")
                        doSoftwareKeyGen(
                            txId,
                            callingUid,
                            keyDescriptor,
                            attestationKey,
                            parsedParams,
                            keyId,
                            isAttestKeyRequest,
                        )
                    }
                    parsedParams.attestationChallenge != null -> {
                        logProbe("PATCH")
                        TransactionResult.Continue
                    }
                    else -> {
                        logProbe("PASSTHROUGH")
                        TransactionResult.Continue
                    }
                }
            }
            .getOrElse { ex ->
                SystemLogger.error("Error during generateKey handling for UID $callingUid.", ex)
                // The dossier only fires on a produced chain; a forge that throws (e.g. a missing
                // keybox) would otherwise leave no per-UID record. Pair this with the preceding
                // `dispatch` line to see which request failed and why.
                SystemLogger.uidLog(callingUid, txId, "forge-fail") { "ex=${ex.message}" }
                // Preserve service-specific KeyMint failures instead of hiding them as -49.
                if (ex is android.os.ServiceSpecificException) {
                    InterceptorUtils.createServiceSpecificErrorReply(ex.errorCode)
                } else {
                    InterceptorUtils.createServiceSpecificErrorReply(SECURE_HW_COMMUNICATION_FAILED)
                }
            }
    }

    private fun doSoftwareKeyGen(
        txId: Long,
        callingUid: Int,
        keyDescriptor: KeyDescriptor,
        attestationKey: KeyDescriptor?,
        parsedParams: KeyMintAttestation,
        keyId: KeyIdentifier,
        isAttestKeyRequest: Boolean,
    ): TransactionResult {
        val genStartNanos = System.nanoTime()
        keyDescriptor.nspace = secureRandom.nextLong()
        SystemLogger.info(
            "Generating software key for ${keyDescriptor.alias}[${keyDescriptor.nspace}]."
        )

        // The alias's previous key stays in place until commitGeneratedKey has stored the new one:
        // any failure on the way (keybox, attest key, provider) leaves the caller's key intact.
        val isSymmetric =
            parsedParams.algorithm != Algorithm.EC && parsedParams.algorithm != Algorithm.RSA

        if (isSymmetric) {
            if (attestationKey != null) {
                throw android.os.ServiceSpecificException(
                    KEYMINT_INVALID_ARGUMENT,
                    "ATTEST_KEY tag is not supported for symmetric algorithms (algo=${parsedParams.algorithm})",
                )
            }
            val algoName =
                when (parsedParams.algorithm) {
                    Algorithm.AES -> "AES"
                    Algorithm.HMAC ->
                        when (parsedParams.digest.firstOrNull()) {
                            Digest.SHA1 -> "HmacSHA1"
                            Digest.SHA_2_224 -> "HmacSHA224"
                            Digest.SHA_2_384 -> "HmacSHA384"
                            Digest.SHA_2_512 -> "HmacSHA512"
                            else -> "HmacSHA256"
                        }
                    else ->
                        throw android.os.ServiceSpecificException(
                            KEYMINT_INVALID_ARGUMENT,
                            "Unsupported symmetric algorithm: ${parsedParams.algorithm}",
                        )
                }
            val keyGen = javax.crypto.KeyGenerator.getInstance(algoName)
            keyGen.init(parsedParams.keySize)
            val secretKey = keyGen.generateKey()

            val metadata =
                KeyMetadata().apply {
                    keySecurityLevel = securityLevel
                    key =
                        KeyDescriptor().apply {
                            domain = Domain.KEY_ID
                            nspace = keyDescriptor.nspace
                            alias = null
                            blob = null
                        }
                    certificate = null
                    certificateChain = null
                    authorizations = parsedParams.toAuthorizations(callingUid, securityLevel)
                    modificationTimeMs = System.currentTimeMillis()
                }
            val response =
                KeyEntryResponse().apply {
                    this.metadata = metadata
                    iSecurityLevel = original
                }
            // Persist symmetric keys too. Without this, AndroidX security
            // crypto MasterKey (AES-GCM-256) is regenerated on every reboot
            // and any EncryptedSharedPreferences becomes undecryptable —
            // which apps that wrap their session token in
            // EncryptedSharedPreferences interpret as session expiry.
            // Snapshot the metadata bytes alongside the raw secret
            // material so authorizations restore byte-identical.
            val metadataBytesForSymmetric =
                runCatching {
                        val parcel = android.os.Parcel.obtain()
                        try {
                            metadata.writeToParcel(parcel, 0)
                            parcel.marshall()
                        } finally {
                            parcel.recycle()
                        }
                    }
                    .getOrNull()
            val info = GeneratedKeyInfo(null, secretKey, keyDescriptor.nspace, response, parsedParams)
            val stored =
                commitGeneratedKey(keyId, info, isAttestationKey = false) {
                    GeneratedKeyPersistence.save(
                        keyId = keyId,
                        keyPair = null,
                        secretKey = secretKey,
                        nspace = keyDescriptor.nspace,
                        securityLevel = securityLevel,
                        certChain = emptyList(),
                        algorithm = parsedParams.algorithm,
                        keySize = parsedParams.keySize,
                        ecCurve = parsedParams.ecCurve ?: 0,
                        purposes = parsedParams.purpose,
                        digests = parsedParams.digest,
                        isAttestationKey = false,
                        metadataBytes = metadataBytesForSymmetric,
                    )
                }
            if (!stored) throw keyNotStored(keyId)

            if (securityLevel == SecurityLevel.STRONGBOX) {
                val delayMs =
                    STRONGBOX_KEYGEN_LATENCY_FLOOR_MS -
                        (System.nanoTime() - genStartNanos) / 1_000_000
                if (delayMs > 0) LockSupport.parkNanos(delayMs * 1_000_000)
            } else {
                TeeLatencySimulator.simulateGenerateKeyDelay(
                    parsedParams.algorithm,
                    System.nanoTime() - genStartNanos,
                )
            }

            return InterceptorUtils.createTypedObjectReply(
                metadata,
                diagnostic = InterceptorUtils.ReplyDiagnostic(callingUid, txId, "genkey-reply-sym"),
            )
        }

        // The framework can designate the attest key by alias OR — for a persistent key the caller
        // reuses across sessions — by KEY_ID with a null alias. Resolve both: the leaf must be
        // signed by the attest key the caller chains to via getCertChain, never silently re-rooted
        // under the keybox (which double-roots the assembled chain and fails verification).
        val attestKeyAlias: String? =
            attestationKey?.let {
                if (it.domain == Domain.GRANT)
                    resolveGrant(it.nspace, callingUid)?.ownerKeyId?.alias
                else it.alias ?: findGeneratedAliasByKeyId(callingUid, it.nspace)
            }
        if (attestationKey != null && attestationKey.domain == Domain.GRANT) {
            SystemLogger.uidLog(callingUid, txId, "attest-grant") {
                "grantId=${attestationKey.nspace} → signer=$attestKeyAlias"
            }
        }
        if (attestationKey != null && attestKeyAlias == null) {
            throw android.os.ServiceSpecificException(
                KEYMINT_INVALID_ARGUMENT,
                "Designated attest key not resolvable (nspace=${attestationKey.nspace}) for uid $callingUid",
            )
        }

        var forgePath = "FORGE-bouncycastle"
        val keyData =
            if (NativeCertGen.isAvailable && attestationKey == null) {
                generateAttestedKeyPairNative(callingUid, parsedParams)?.also {
                    forgePath = "FORGE-rust"
                }
                    ?: CertificateGenerator.generateAttestedKeyPair(
                        callingUid,
                        keyDescriptor.alias,
                        attestKeyAlias,
                        parsedParams,
                        securityLevel,
                    )
            } else {
                CertificateGenerator.generateAttestedKeyPair(
                    callingUid,
                    keyDescriptor.alias,
                    attestKeyAlias,
                    parsedParams,
                    securityLevel,
                )
            } ?: throw Exception("Both native and BouncyCastle cert gen failed.")

        // FORGE decode point: dump the dossier of the chain we just forged, tagged with the forger
        // that produced it. uid + txId are both in scope here, so this is the cheapest place to
        // capture ground truth for a generate-mode app.
        AttestationDossier.log(callingUid, txId, forgePath, keyData.second)

        val response =
            buildKeyEntryResponse(callingUid, keyData.second, parsedParams, keyDescriptor)
        AttestationDossier.logAuthShape(callingUid, txId, response.metadata?.authorizations)

        if (SystemLogger.isDebugBuild) {
            val chain = keyData.second
            val leaf = chain.firstOrNull() as? java.security.cert.X509Certificate
            SystemLogger.trace {
                "[certchain] ${keyDescriptor.alias}: depth=${chain.size} " +
                    "issuer=${leaf?.issuerX500Principal?.name} " +
                    "subject=${leaf?.subjectX500Principal?.name} " +
                    "hasAttest=${leaf?.getExtensionValue("1.3.6.1.4.1.11129.2.1.17") != null}"
            }
        }

        val certChainCopy = keyData.second.toList()
        // Snapshot the freshly built KeyMetadata bytes so loadPersistedKeys
        // can restore byte-identical authorizations after reboot. Without
        // this, the rebuild path drops every authorization tag that wasn't
        // captured into PersistedKeyData primitive fields (origin, block
        // mode, padding, expiry timestamps...), which broke session pinning
        // for apps that fingerprint metadata across keystore calls.
        val metadataBytesForPersist =
            response.metadata?.let { md ->
                runCatching {
                        val parcel = android.os.Parcel.obtain()
                        try {
                            md.writeToParcel(parcel, 0)
                            parcel.marshall()
                        } finally {
                            parcel.recycle()
                        }
                    }
                    .getOrNull()
            }
        val info = GeneratedKeyInfo(keyData.first, null, keyDescriptor.nspace, response, parsedParams)
        val stored =
            commitGeneratedKey(keyId, info, isAttestKeyRequest) {
                GeneratedKeyPersistence.save(
                    keyId = keyId,
                    keyPair = keyData.first,
                    secretKey = null,
                    nspace = keyDescriptor.nspace,
                    securityLevel = securityLevel,
                    certChain = certChainCopy,
                    algorithm = parsedParams.algorithm,
                    keySize = parsedParams.keySize,
                    ecCurve = parsedParams.ecCurve ?: 0,
                    purposes = parsedParams.purpose,
                    digests = parsedParams.digest,
                    isAttestationKey = isAttestKeyRequest,
                    metadataBytes = metadataBytesForPersist,
                )
            }
        if (!stored) throw keyNotStored(keyId)

        if (securityLevel == SecurityLevel.STRONGBOX) {
            val delayMs =
                STRONGBOX_KEYGEN_LATENCY_FLOOR_MS - (System.nanoTime() - genStartNanos) / 1_000_000
            if (delayMs > 0) LockSupport.parkNanos(delayMs * 1_000_000)
        } else {
            TeeLatencySimulator.simulateGenerateKeyDelay(
                parsedParams.algorithm,
                System.nanoTime() - genStartNanos,
            )
        }

        return InterceptorUtils.createTypedObjectReply(
            response.metadata,
            diagnostic = InterceptorUtils.ReplyDiagnostic(callingUid, txId, "genkey-reply-asym"),
        )
    }

    private fun generateAttestedKeyPairNative(
        callingUid: Int,
        params: KeyMintAttestation,
    ): AndroidPair<KeyPair, List<Certificate>>? {
        return runCatching {
                val algorithmName =
                    when (params.algorithm) {
                        Algorithm.EC -> "EC"
                        Algorithm.RSA -> "RSA"
                        else -> return null
                    }
                val keyboxFile = ConfigurationManager.getKeyboxFileForUid(callingUid)
                val keybox =
                    KeyBoxManager.getAttestationKey(keyboxFile, algorithmName) ?: return null

                val keyboxPrivateKeyBytes = keybox.keyPair.private.encoded
                val keyboxCertChainBytes =
                    keybox.certificates
                        .map { it.encoded }
                        .fold(ByteArray(0)) { acc, der -> acc + der }

                val attestVersion = AndroidDeviceUtils.getAttestVersion(securityLevel)
                val keymasterVersion = AndroidDeviceUtils.getKeymasterVersion(securityLevel)
                val hasChallenge = params.attestationChallenge != null
                val appId =
                    if (hasChallenge) AttestationBuilder.createApplicationId(callingUid) else null

                val config =
                    CertGenConfig(
                        algorithm = params.algorithm,
                        keySize = params.keySize,
                        ecCurve = params.ecCurve ?: 0,
                        rsaPublicExponent = params.rsaPublicExponent?.toLong() ?: 65537L,
                        attestationChallenge = params.attestationChallenge,
                        purposes = params.purpose.toIntArray(),
                        digests = params.digest.toIntArray(),
                        certSerial = params.certificateSerial?.toByteArray(),
                        certSubject = params.certificateSubject?.encoded,
                        certNotBefore = params.certificateNotBefore?.time ?: -1L,
                        certNotAfter = params.certificateNotAfter?.time ?: -1L,
                        keyboxPrivateKey = keyboxPrivateKeyBytes,
                        keyboxCertChain = keyboxCertChainBytes,
                        securityLevel = securityLevel,
                        attestVersion = attestVersion,
                        keymasterVersion = keymasterVersion,
                        osVersion = AndroidDeviceUtils.osVersion,
                        osPatchLevel = AndroidDeviceUtils.getPatchLevel(callingUid),
                        vendorPatchLevel = AndroidDeviceUtils.getVendorPatchLevelLong(callingUid),
                        bootPatchLevel = AndroidDeviceUtils.getBootPatchLevelLong(callingUid),
                        bootKey = AndroidDeviceUtils.bootKey,
                        bootHash = AndroidDeviceUtils.bootHash,
                        creationDatetime = System.currentTimeMillis(),
                        attestationApplicationId = appId?.octets ?: ByteArray(0),
                        moduleHash =
                            if (attestVersion >= 400) AndroidDeviceUtils.moduleHash else null,
                        idBrand = params.brand,
                        idDevice = params.device,
                        idProduct = params.product,
                        idSerial = params.serial,
                        idImei = params.imei,
                        idMeid = params.meid,
                        idManufacturer = params.manufacturer,
                        idModel = params.model,
                        idSecondImei = if (attestVersion >= 300) params.secondImei else null,
                        activeDatetime = params.activeDateTime?.time ?: -1L,
                        originationExpireDatetime = params.originationExpireDateTime?.time ?: -1L,
                        usageExpireDatetime = params.usageExpireDateTime?.time ?: -1L,
                        usageCountLimit = params.usageCountLimit ?: -1,
                        callerNonce = params.callerNonce == true,
                        unlockedDeviceRequired = params.unlockedDeviceRequired == true,
                        noAuthRequired = params.noAuthRequired == true,
                        userAuthType = params.userAuthType?.let { it.toLong() and 0xFFFFFFFFL } ?: -1L,
                        authTimeout = params.authTimeout ?: -1,
                        uid = callingUid,
                        debugLogging = SystemLogger.isDebugBuild,
                    )

                val resultBytes = NativeCertGen.generateAttestedKeyPair(config) ?: return null
                val (keyPair, certs) = NativeCertGen.parseNativeResult(resultBytes)
                SystemLogger.info(
                    "NativeCertGen: generated key pair successfully (${certs.size} certs)"
                )
                AndroidPair(keyPair, certs)
            }
            .onFailure {
                SystemLogger.error(
                    "NativeCertGen: generation failed, falling back to BouncyCastle",
                    it,
                )
            }
            .getOrNull()
    }

    private fun buildKeyEntryResponse(
        callingUid: Int,
        chain: List<Certificate>,
        params: KeyMintAttestation,
        descriptor: KeyDescriptor,
    ): KeyEntryResponse {
        val normalizedKeyDescriptor =
            KeyDescriptor().apply {
                domain = Domain.KEY_ID
                nspace = descriptor.nspace
                alias = null
                blob = null
            }
        val metadata =
            KeyMetadata().apply {
                keySecurityLevel = securityLevel
                key = normalizedKeyDescriptor
                CertificateHelper.updateCertificateChain(this, chain.toTypedArray()).getOrThrow()
                authorizations = params.toAuthorizations(callingUid, securityLevel)
                modificationTimeMs = System.currentTimeMillis()
            }
        return KeyEntryResponse().apply {
            this.metadata = metadata
            iSecurityLevel = original
        }
    }

    fun loadPersistedKeys() {
        val records = GeneratedKeyPersistence.loadAll(securityLevel)
        if (records.isEmpty()) {
            SystemLogger.debug("No persisted keys to restore for security level $securityLevel")
            return
        }

        SystemLogger.info(
            "Restoring ${records.size} persisted keys for security level $securityLevel"
        )

        for (record in records) {
            runCatching {
                    val keyId = KeyIdentifier(record.uid, record.alias)
                    if (generatedKeys.containsKey(keyId)) {
                        SystemLogger.debug("Skipping already-loaded key: $keyId")
                        return@runCatching
                    }

                    // Symmetric (AES/HMAC/3DES) keys take a separate path:
                    // there is no PKCS8 private key, no certificate chain, just
                    // raw secret material plus the metadata snapshot.
                    val isSymmetric = record.symmetricKeyBytes.isNotEmpty()
                    if (isSymmetric) {
                        val secretKey =
                            javax.crypto.spec.SecretKeySpec(
                                record.symmetricKeyBytes,
                                record.symmetricAlgorithm,
                            )
                        val response =
                            if (record.metadataBytes.isNotEmpty()) {
                                runCatching {
                                        val parcel = android.os.Parcel.obtain()
                                        try {
                                            parcel.unmarshall(
                                                record.metadataBytes,
                                                0,
                                                record.metadataBytes.size,
                                            )
                                            parcel.setDataPosition(0)
                                            val metadata =
                                                KeyMetadata.CREATOR.createFromParcel(parcel)
                                            KeyEntryResponse().apply {
                                                this.metadata = metadata
                                                iSecurityLevel = original
                                            }
                                        } finally {
                                            parcel.recycle()
                                        }
                                    }
                                    .getOrElse { e ->
                                        SystemLogger.warning(
                                            "Failed to restore symmetric metadata for ${record.alias}, falling back to primitive rebuild",
                                            e,
                                        )
                                        rebuildSymmetricResponse(record)
                                    }
                            } else {
                                // Pre-v3 file with symmetric key — should not happen
                                // because v3 always saves metadata, but be defensive:
                                // rebuild a minimal KeyMetadata from primitives so
                                // the secret material is still restored. Without
                                // this, dropping the record would silently log the
                                // user out the next time the alias is used.
                                SystemLogger.info(
                                    "Symmetric record ${record.alias} missing metadata bytes, rebuilding from primitives"
                                )
                                rebuildSymmetricResponse(record)
                            }
                        generatedKeys[keyId] =
                            GeneratedKeyInfo(
                                keyPair = null,
                                secretKey = secretKey,
                                nspace = record.nspace,
                                response = response,
                                keyParams =
                                    response.metadata?.let { md ->
                                        KeyMintAttestation(
                                            md.authorizations
                                                ?.map { it.keyParameter }
                                                ?.toTypedArray() ?: emptyArray()
                                        )
                                    },
                            )
                        SystemLogger.debug(
                            "Restored symmetric persisted key: $keyId (${record.symmetricAlgorithm}/${record.symmetricKeyBytes.size * 8}bit)"
                        )
                        return@runCatching
                    }

                    val algorithmName =
                        when (record.algorithm) {
                            Algorithm.EC -> "EC"
                            Algorithm.RSA -> "RSA"
                            else ->
                                throw IllegalArgumentException(
                                    "Unknown algorithm: ${record.algorithm}"
                                )
                        }

                    val keyFactory = KeyFactory.getInstance(algorithmName)
                    val privateKey =
                        keyFactory.generatePrivate(PKCS8EncodedKeySpec(record.privateKeyBytes))

                    val certFactory = CertificateFactory.getInstance("X.509")
                    val certChain =
                        record.certChainBytes.map { bytes ->
                            certFactory.generateCertificate(ByteArrayInputStream(bytes))
                        }
                    require(certChain.isNotEmpty()) { "Persisted key has empty certificate chain" }

                    val publicKey = certChain[0].publicKey
                    // The private key ($algorithmName) signs leaves that callers verify against this
                    // served chain's leaf public key. If the two disagree (EC private under an RSA
                    // served leaf) every signature this key makes fails as DATA_TOO_LARGE_FOR_MODULUS
                    // -- the A16 EC two-root. A split record is corrupt: drop it so the next
                    // generateKey rebirths a coherent one rather than serve a key that cannot sign.
                    require(publicKey.algorithm == algorithmName) {
                        "Persisted key ${record.alias} splits private=$algorithmName " +
                            "vs served leaf=${publicKey.algorithm}; dropping"
                    }
                    val keyPair = KeyPair(publicKey, privateKey)

                    val descriptor =
                        KeyDescriptor().apply {
                            domain = Domain.APP
                            nspace = record.nspace
                            alias = record.alias
                            blob = null
                        }

                    // Prefer the byte-identical metadata snapshot persisted by v3
                    // saves so apps that fingerprint the metadata (e.g. they
                    // pin algorithm/purpose/digest/origin/authorization order
                    // across reboots) keep their session valid. Fall back to
                    // rebuilding
                    // from primitive fields for v1-era files (which lose
                    // authorization tags that weren't captured then).
                    val response =
                        if (record.metadataBytes.isNotEmpty()) {
                            runCatching {
                                    val parcel = android.os.Parcel.obtain()
                                    try {
                                        parcel.unmarshall(
                                            record.metadataBytes,
                                            0,
                                            record.metadataBytes.size,
                                        )
                                        parcel.setDataPosition(0)
                                        val metadata = KeyMetadata.CREATOR.createFromParcel(parcel)
                                        // Make sure the descriptor's nspace matches the
                                        // KEY_ID we will hand callers. updateSubcomponent
                                        // and getKeyEntry both index by nspace.
                                        metadata.key =
                                            metadata.key
                                                ?: KeyDescriptor().apply {
                                                    domain = Domain.KEY_ID
                                                    nspace = record.nspace
                                                    alias = null
                                                    blob = null
                                                }
                                        KeyEntryResponse().apply {
                                            this.metadata = metadata
                                            iSecurityLevel = original
                                        }
                                    } finally {
                                        parcel.recycle()
                                    }
                                }
                                .getOrElse { e ->
                                    SystemLogger.warning(
                                        "Failed to restore metadata bytes for $record.alias, falling back to rebuild",
                                        e,
                                    )
                                    rebuildResponseFromRecord(record, certChain, descriptor)
                                }
                        } else {
                            rebuildResponseFromRecord(record, certChain, descriptor)
                        }

                    val keyIdRestored = KeyIdentifier(record.uid, record.alias)
                    generatedKeys[keyIdRestored] =
                        GeneratedKeyInfo(
                            keyPair,
                            null,
                            record.nspace,
                            response,
                            response.metadata?.let { md ->
                                // Re-derive an attestation summary from authorizations so
                                // any code path that reads keyParams (e.g. logging) still
                                // works. This does not feed back into the metadata bytes.
                                KeyMintAttestation(
                                    md.authorizations?.map { it.keyParameter }?.toTypedArray()
                                        ?: emptyArray()
                                )
                            },
                        )
                    if (record.isAttestationKey) attestationKeys.add(keyIdRestored)

                    SystemLogger.debug("Restored persisted key: $keyIdRestored")
                }
                .onFailure {
                    SystemLogger.error(
                        "Failed to restore key: uid=${record.uid} alias=${record.alias}",
                        it,
                    )
                }
        }

        SystemLogger.info("Key restoration complete. Total in memory: ${generatedKeys.size}")
    }

    /**
     * Fallback rebuild path used when no v3 metadata snapshot is available (key was saved by an
     * older build, or the snapshot failed to deserialize). Rebuilds KeyEntryResponse from primitive
     * fields. This loses any authorization tags that weren't captured at save time, which is why we
     * prefer the byte-identical v3 snapshot whenever possible.
     */
    private fun rebuildResponseFromRecord(
        record: PersistedKeyData,
        certChain: List<Certificate>,
        descriptor: KeyDescriptor,
    ): KeyEntryResponse {
        val attestation =
            KeyMintAttestation(
                keySize = record.keySize,
                algorithm = record.algorithm,
                ecCurve = record.ecCurve,
                ecCurveName = "",
                origin = null,
                blockMode = emptyList(),
                padding = emptyList(),
                purpose = record.purposes,
                digest = record.digests,
                rsaPublicExponent = null,
                certificateSerial = null,
                certificateSubject = null,
                certificateNotBefore = null,
                certificateNotAfter = null,
                attestationChallenge = null,
                brand = null,
                device = null,
                product = null,
                serial = null,
                imei = null,
                meid = null,
                manufacturer = null,
                model = null,
                secondImei = null,
                activeDateTime = null,
                originationExpireDateTime = null,
                usageExpireDateTime = null,
                usageCountLimit = null,
                callerNonce = null,
                nonce = null,
                unlockedDeviceRequired = null,
                includeUniqueId = null,
                rollbackResistance = null,
                earlyBootOnly = null,
                allowWhileOnBody = null,
                trustedUserPresenceRequired = null,
                trustedConfirmationRequired = null,
                noAuthRequired = true, // no auth tags to restore; keep pre-fix default
                maxUsesPerBoot = null,
                maxBootLevel = null,
                minMacLength = null,
                rsaOaepMgfDigest = emptyList(),
            )
        return buildKeyEntryResponse(record.uid, certChain, attestation, descriptor)
    }

    /**
     * Defensive fallback for symmetric key records that somehow ended up without a metadata
     * snapshot (e.g. a save where Parcel.marshall() threw and persisted an empty mdBytes, or a
     * future format where the snapshot is lazily populated). Without this fallback, loadAll would
     * skip the record and the secret material would be effectively lost, silently logging the user
     * out the next time the alias is used.
     *
     * The rebuilt KeyMetadata is structurally minimal — only the primitive authorization tags we
     * captured at save time. That's worse than a byte-identical snapshot for apps that fingerprint
     * metadata, but it still keeps the AES key alive across reboots, which is the dominant
     * correctness concern.
     */
    private fun rebuildSymmetricResponse(record: PersistedKeyData): KeyEntryResponse {
        val attestation =
            KeyMintAttestation(
                keySize = record.keySize,
                algorithm = record.algorithm,
                ecCurve = record.ecCurve,
                ecCurveName = "",
                origin = null,
                blockMode = emptyList(),
                padding = emptyList(),
                purpose = record.purposes,
                digest = record.digests,
                rsaPublicExponent = null,
                certificateSerial = null,
                certificateSubject = null,
                certificateNotBefore = null,
                certificateNotAfter = null,
                attestationChallenge = null,
                brand = null,
                device = null,
                product = null,
                serial = null,
                imei = null,
                meid = null,
                manufacturer = null,
                model = null,
                secondImei = null,
                activeDateTime = null,
                originationExpireDateTime = null,
                usageExpireDateTime = null,
                usageCountLimit = null,
                callerNonce = null,
                nonce = null,
                unlockedDeviceRequired = null,
                includeUniqueId = null,
                rollbackResistance = null,
                earlyBootOnly = null,
                allowWhileOnBody = null,
                trustedUserPresenceRequired = null,
                trustedConfirmationRequired = null,
                noAuthRequired = true, // no auth tags to restore; keep pre-fix default
                maxUsesPerBoot = null,
                maxBootLevel = null,
                minMacLength = null,
                rsaOaepMgfDigest = emptyList(),
            )
        val metadata =
            KeyMetadata().apply {
                keySecurityLevel = securityLevel
                key =
                    KeyDescriptor().apply {
                        domain = Domain.KEY_ID
                        nspace = record.nspace
                        alias = null
                        blob = null
                    }
                certificate = null
                certificateChain = null
                authorizations = attestation.toAuthorizations(record.uid, securityLevel)
                modificationTimeMs = System.currentTimeMillis()
            }
        return KeyEntryResponse().apply {
            this.metadata = metadata
            iSecurityLevel = original
        }
    }

    companion object {
        private val secureRandom = SecureRandom()

        // Maximum alias length to prevent binder buffer exhaustion (Issue #109)
        // Binder buffer is ~1MB; 256KB provides 4x safety margin for transaction overhead
        private const val MAX_ALIAS_LENGTH = 256 * 1024
        private const val KEYMINT_INVALID_INPUT_LENGTH = -21
        private const val KEYMINT_INVALID_ARGUMENT = -38
        private const val RESPONSE_INVALID_ARGUMENT = 20
        private const val RESPONSE_PERMISSION_DENIED = 6
        private const val RESPONSE_KEY_NOT_FOUND = 7
        private const val KEY_PERMISSION_USE = 0x100
        private const val TEE_LATENCY_FLOOR_MS = 15L
        private const val STRONGBOX_KEYGEN_LATENCY_FLOOR_MS = 250L
        private const val STRONGBOX_OP_LATENCY_FLOOR_MS = 80L
        private const val TEE_OP_LATENCY_FLOOR_MS = 4L
        private const val KEYMINT_CANNOT_ATTEST_IDS = -66
        private const val KEYMINT_UNKNOWN_ERROR = -1000
        private const val SECURE_HW_COMMUNICATION_FAILED = -49
        private const val MAX_CONCURRENT_OPS_PER_UID = 15
        private const val STRONGBOX_MAX_CONCURRENT_OPS = 4

        private fun keyNotStored(keyId: KeyIdentifier) =
            android.os.ServiceSpecificException(
                SECURE_HW_COMMUNICATION_FAILED,
                "Generated key $keyId could not be stored; the previous key is kept",
            )

        private fun isStrongBoxCapable(params: KeyMintAttestation): Boolean =
            when (params.algorithm) {
                Algorithm.RSA -> params.keySize <= 2048
                Algorithm.EC -> params.ecCurve == null || params.ecCurve == EcCurve.P_256
                else -> true
            }

        private val GENERATE_KEY_TRANSACTION =
            InterceptorUtils.getTransactCode(IKeystoreSecurityLevel.Stub::class.java, "generateKey")
        private val IMPORT_KEY_TRANSACTION =
            InterceptorUtils.getTransactCode(IKeystoreSecurityLevel.Stub::class.java, "importKey")
        private val IMPORT_WRAPPED_KEY_TRANSACTION =
            InterceptorUtils.getTransactCode(
                IKeystoreSecurityLevel.Stub::class.java,
                "importWrappedKey",
            )
        private val CREATE_OPERATION_TRANSACTION =
            InterceptorUtils.getTransactCode(
                IKeystoreSecurityLevel.Stub::class.java,
                "createOperation",
            )

        val INTERCEPTED_CODES =
            intArrayOf(
                GENERATE_KEY_TRANSACTION,
                IMPORT_KEY_TRANSACTION,
                IMPORT_WRAPPED_KEY_TRANSACTION,
                CREATE_OPERATION_TRANSACTION,
            )

        private val transactionNames: Map<Int, String> by lazy {
            IKeystoreSecurityLevel.Stub::class
                .java
                .declaredFields
                .filter {
                    it.isAccessible = true
                    it.type == Int::class.java && it.name.startsWith("TRANSACTION_")
                }
                .associate { field -> (field.get(null) as Int) to field.name.split("_")[1] }
        }

        private val persistExecutor = Executors.newSingleThreadExecutor()

        /**
         * Runs persistence I/O on the single persist thread. Saves and deletes must share it: a
         * synchronous delete could otherwise overtake a still-queued save and the deleted key would
         * be written back.
         */
        fun persist(task: () -> Unit) = persistExecutor.execute(task)

        /**
         * Makes a freshly generated software key the alias's key. The file is written first and
         * the previous key is dropped only after that succeeded, so a failed generation or a full
         * disk never costs the caller the key it already had, and a reply of success means the key
         * survives a reboot. Running on the persist thread orders the swap with every other save
         * and delete of the alias, so concurrent generations leave memory and disk agreeing.
         *
         * @return false when the key could not be stored; nothing was changed then.
         */
        fun commitGeneratedKey(
            keyId: KeyIdentifier,
            info: GeneratedKeyInfo,
            isAttestationKey: Boolean,
            save: () -> Boolean,
        ): Boolean =
            persistExecutor
                .submit(
                    Callable {
                        if (!save()) return@Callable false
                        cleanupKeyData(keyId, deleteFile = false)
                        generatedKeys[keyId] = info
                        if (isAttestationKey) attestationKeys.add(keyId)
                        true
                    }
                )
                .get()

        val generatedKeys = ConcurrentHashMap<KeyIdentifier, GeneratedKeyInfo>()
        val teeResponses = ConcurrentHashMap<KeyIdentifier, KeyEntryResponse>()
        val patchedChains = ConcurrentHashMap<KeyIdentifier, Array<Certificate>>()
        val attestationKeys: MutableSet<KeyIdentifier> = ConcurrentHashMap.newKeySet()
        val importedKeys: MutableSet<KeyIdentifier> = ConcurrentHashMap.newKeySet()
        private val interceptedOperations = ConcurrentHashMap<IBinder, OperationInterceptor>()

        /**
         * Grant plane for the public `KeyStoreManager.grantKeyAccess()` API (Android 16, API 36+).
         * On Android <= 15 grant was a hidden API denied to untrusted_app, so this state stays
         * empty there (the GRANT_TRANSACTION handler returns PERMISSION_DENIED for synthetic keys
         * pre-36). A grant is caller-bound and carries an access vector; resolving one yields the
         * owner's own KeyEntryResponse so every access plane returns a coherent certificate chain.
         */
        data class SoftwareGrant(
            val ownerKeyId: KeyIdentifier,
            val granteeUid: Int,
            val accessVector: Int,
        )

        val softwareGrants = ConcurrentHashMap<Long, SoftwareGrant>() // grantId -> grant

        /** Mint or reuse a grant id (random, non-zero, non -1 Long). Re-grant reuses the id. */
        fun issueGrant(ownerKeyId: KeyIdentifier, granteeUid: Int, accessVector: Int): Long {
            softwareGrants.entries
                .firstOrNull {
                    it.value.ownerKeyId == ownerKeyId && it.value.granteeUid == granteeUid
                }
                ?.let { existing ->
                    softwareGrants[existing.key] = existing.value.copy(accessVector = accessVector)
                    return existing.key
                }
            var id = secureRandom.nextLong()
            while (id == 0L || id == -1L || softwareGrants.containsKey(id)) id =
                secureRandom.nextLong()
            softwareGrants[id] = SoftwareGrant(ownerKeyId, granteeUid, accessVector)
            return id
        }

        /** Caller-bound resolve: only the designated grantee, only while the key exists. */
        /** A software key granted to [callerUid], addressed by the KEY_ID its metadata names. */
        fun findGrantedKeyByKeyId(
            callerUid: Int,
            nspace: Long?,
        ): Pair<SoftwareGrant, GeneratedKeyInfo>? {
            if (nspace == null || nspace == 0L) return null
            return softwareGrants.values.firstNotNullOfOrNull { grant ->
                if (grant.granteeUid != callerUid) null
                else generatedKeys[grant.ownerKeyId]?.takeIf { it.nspace == nspace }?.let { grant to it }
            }
        }

        fun resolveGrant(grantId: Long, callerUid: Int): SoftwareGrant? =
            softwareGrants[grantId]?.takeIf {
                it.granteeUid == callerUid && ownsKeyResponse(it.ownerKeyId)
            }

        /**
         * True when this interceptor holds a coherent [KeyEntryResponse] for [keyId] — synthetic
         * (`generatedKeys`) OR patch-mode (`teeResponses`, a real TEE key whose attestation we
         * patched). The grant plane must virtualize both: gating on `generatedKeys` alone left
         * patch-mode keys' `Domain.GRANT` readback falling through to the real keystore2 unpatched,
         * splitting the grant chain against the owner's patched read (duck
         * SELF_/ISOLATED_CHAIN_SPLIT, surfaced once Android 16 made KeyStoreManager.grantKeyAccess
         * a public API).
         */
        fun ownsKeyResponse(keyId: KeyIdentifier): Boolean = getGeneratedKeyResponse(keyId) != null

        fun revokeGrant(ownerKeyId: KeyIdentifier, granteeUid: Int) {
            softwareGrants.entries
                .filter { it.value.ownerKeyId == ownerKeyId && it.value.granteeUid == granteeUid }
                .forEach { softwareGrants.remove(it.key) }
        }

        fun purgeGrantsForKey(ownerKeyId: KeyIdentifier) {
            softwareGrants.entries
                .filter { it.value.ownerKeyId == ownerKeyId }
                .forEach { softwareGrants.remove(it.key) }
        }

        fun getGeneratedKeyResponse(keyId: KeyIdentifier): KeyEntryResponse? =
            generatedKeys[keyId]?.response ?: teeResponses[keyId]

        fun findGeneratedKeyByKeyId(callingUid: Int, nspace: Long?): GeneratedKeyInfo? {
            if (nspace == null || nspace == 0L) return null
            return generatedKeys.entries
                .filter { (keyIdentifier, _) -> keyIdentifier.uid == callingUid }
                .find { (_, info) -> info.nspace == nspace }
                ?.value
        }

        /**
         * Resolves the alias of a generated key addressed by KEY_ID. The framework hands a reused
         * (persistent) attest key to generateKey as a KEY_ID descriptor with a null alias; this
         * maps it back to the alias our cache is keyed by, so the leaf is signed by the attest key
         * the caller will chain to rather than silently re-rooted under the keybox.
         */
        fun findGeneratedAliasByKeyId(callingUid: Int, nspace: Long?): String? {
            if (nspace == null || nspace == 0L) return null
            return generatedKeys.entries
                .firstOrNull { (keyId, info) -> keyId.uid == callingUid && info.nspace == nspace }
                ?.key
                ?.alias
        }

        fun findTeeResponseByKeyId(callingUid: Int, nspace: Long?): KeyEntryResponse? {
            if (nspace == null || nspace == 0L) return null
            return teeResponses.entries
                .filter { (keyId, _) -> keyId.uid == callingUid }
                .find { (_, response) -> response.metadata?.key?.nspace == nspace }
                ?.value
        }

        /**
         * Drops the cached TEE/patched response (and patched chain) addressed by KEY_ID so a
         * post-mutation getKeyEntry falls through to the now-updated real keystore2 key. Used after
         * updateSubcomponent re-keys a patched chain (duck STALE_TEE_RESPONSE_AFTER_KEY_ID_UPDATE).
         */
        fun evictTeeResponseByKeyId(callingUid: Int, nspace: Long?) {
            if (nspace == null || nspace == 0L) return
            teeResponses.entries
                .filter { (keyId, _) -> keyId.uid == callingUid }
                .find { (_, response) -> response.metadata?.key?.nspace == nspace }
                ?.let { evictTeeResponse(it.key) }
        }

        /** Alias-addressed counterpart of [evictTeeResponseByKeyId]. */
        fun evictTeeResponse(keyId: KeyIdentifier) {
            teeResponses.remove(keyId)
            patchedChains.remove(keyId)
        }

        fun getPatchedChain(keyId: KeyIdentifier): Array<Certificate>? = patchedChains[keyId]

        fun isAttestationKey(keyId: KeyIdentifier): Boolean = attestationKeys.contains(keyId)

        /**
         * Drops everything cached for [keyId]. [deleteFile] is false only when the caller has just
         * written the alias's replacement file, which a queued delete would destroy.
         */
        fun cleanupKeyData(keyId: KeyIdentifier, deleteFile: Boolean = true) {
            purgeGrantsForKey(keyId) // grants die with the key (Android 16 path; no-op pre-36)
            if (generatedKeys.remove(keyId) != null) {
                SystemLogger.debug("Remove generated key ${keyId}")
                // A generation committed for the alias after this removal (commits run on the
                // persistence thread too) owns the file now; deleting it would lose that key on
                // the next boot.
                if (deleteFile)
                    persist {
                        if (!generatedKeys.containsKey(keyId)) GeneratedKeyPersistence.delete(keyId)
                    }
            }
            teeResponses.remove(keyId)
            if (patchedChains.remove(keyId) != null) {
                SystemLogger.debug("Remove patched chain for ${keyId}")
            }
            if (attestationKeys.remove(keyId)) {
                SystemLogger.debug("Remove cached attestaion key ${keyId}")
            }
            importedKeys.remove(keyId)
        }

        /** Whether anything is cached for [keyId]: a software key or a real key's metadata. */
        fun hasCachedKey(keyId: KeyIdentifier): Boolean =
            generatedKeys.containsKey(keyId) ||
                teeResponses.containsKey(keyId) ||
                patchedChains.containsKey(keyId) ||
                importedKeys.contains(keyId)

        private fun cachedKeyIds(): Set<KeyIdentifier> =
            generatedKeys.keys + teeResponses.keys + patchedChains.keys + importedKeys +
                attestationKeys

        /**
         * Clears everything cached for [uid] (maintenance.clearNamespace, Domain.APP): software
         * keys and the metadata cached for its real keys alike. Clearing an app's data or
         * uninstalling it deletes those real keys, so a cached response would name a key id that
         * keystore2 no longer has.
         */
        fun clearNamespaceKeys(uid: Int) {
            val victims = cachedKeyIds().filter { it.uid == uid }
            victims.forEach { cleanupKeyData(it) } // also purges grants + persistence
            softwareGrants.entries
                .filter { it.value.granteeUid == uid }
                .forEach { softwareGrants.remove(it.key) }
            Keystore2Interceptor.forgetUid(uid)
            if (victims.isNotEmpty())
                SystemLogger.info(
                    "Cleared ${victims.size} cached keys for uid=$uid (maintenance.clearNamespace)"
                )
        }

        /**
         * Removes every key of Android user [userId] (maintenance.onUserRemoved). The files are
         * moved to the backup directory rather than deleted, and the user id may be reused later:
         * left in place, the keys would surface for whichever app is installed under the old uid.
         */
        fun clearUserKeys(userId: Int) {
            val uids = cachedKeyIds().filter { it.uid / 100000 == userId }.map { it.uid }.toSet()
            for (uid in uids) {
                val software = generatedKeys.keys.filter { it.uid == uid }
                software.forEach { keyId ->
                    generatedKeys.remove(keyId)
                    persist {
                        if (!generatedKeys.containsKey(keyId))
                            GeneratedKeyPersistence.archive(keyId, "user$userId-removed")
                    }
                }
                clearNamespaceKeys(uid)
            }
            // A uid that only holds a grant has nothing cached of its own, so the loop above never
            // reaches it; its grants must not outlive the user either.
            softwareGrants.entries.removeIf { (_, grant) ->
                grant.granteeUid / 100000 == userId || grant.ownerKeyId.uid / 100000 == userId
            }
            if (uids.isNotEmpty())
                SystemLogger.info("Cleared cached keys of ${uids.size} uids for removed user $userId")
        }

        /** The alias of a real key whose metadata is cached, addressed by KEY_ID. */
        fun findTeeKeyIdByKeyId(callingUid: Int, nspace: Long?): KeyIdentifier? {
            if (nspace == null || nspace == 0L) return null
            return teeResponses.entries
                .firstOrNull { (keyId, response) ->
                    keyId.uid == callingUid && response.metadata?.key?.nspace == nspace
                }
                ?.key
        }

        /**
         * Re-keys a synthetic entry from [srcId] to [dstId] for maintenance.migrateKeyNamespace,
         * preserving the key material, certificate chain, and any grants (which reference the key,
         * not the namespace). The key is stored under [dstId] before the [srcId] file goes, so it
         * survives a reboot. No-op if [srcId] is not ours or [dstId] already exists.
         */
        fun migrateGeneratedKey(srcId: KeyIdentifier, dstId: KeyIdentifier) {
            if (srcId == dstId || generatedKeys.containsKey(dstId)) return
            val info = generatedKeys[srcId] ?: return
            val isAttestKey = attestationKeys.contains(srcId)
            persist {
                // The source may have been deleted, exhausted or replaced while this waited; a
                // stale instance must not be written back under the destination.
                if (generatedKeys[srcId] !== info || generatedKeys.containsKey(dstId)) return@persist
                if (!saveGeneratedKey(dstId, info, isAttestKey)) {
                    SystemLogger.error("Could not store migrated key $dstId; keeping $srcId")
                    return@persist
                }
                generatedKeys.remove(srcId)
                generatedKeys[dstId] = info
                if (attestationKeys.remove(srcId)) attestationKeys.add(dstId)
                if (importedKeys.remove(srcId)) importedKeys.add(dstId)
                softwareGrants.entries
                    .filter { it.value.ownerKeyId == srcId }
                    .forEach { softwareGrants[it.key] = it.value.copy(ownerKeyId = dstId) }
                GeneratedKeyPersistence.delete(srcId)
                SystemLogger.info(
                    "Migrated synthetic key $srcId -> $dstId (maintenance.migrateKeyNamespace)"
                )
            }
        }

        /** Writes [info] to disk as [keyId], from the state the interceptor holds in memory. */
        private fun saveGeneratedKey(
            keyId: KeyIdentifier,
            info: GeneratedKeyInfo,
            isAttestKey: Boolean,
        ): Boolean {
            val metadata = info.response.metadata ?: return false
            val params = info.keyParams
            val metadataBytes =
                runCatching {
                        val parcel = Parcel.obtain()
                        try {
                            metadata.writeToParcel(parcel, 0)
                            parcel.marshall()
                        } finally {
                            parcel.recycle()
                        }
                    }
                    .getOrNull()
            return GeneratedKeyPersistence.save(
                keyId = keyId,
                keyPair = info.keyPair,
                secretKey = info.secretKey,
                nspace = info.nspace,
                securityLevel = metadata.keySecurityLevel,
                certChain = CertificateHelper.getCertificateChain(metadata)?.toList() ?: emptyList(),
                algorithm = params?.algorithm ?: 0,
                keySize = params?.keySize ?: 0,
                ecCurve = params?.ecCurve ?: 0,
                purposes = params?.purpose ?: emptyList(),
                digests = params?.digest ?: emptyList(),
                isAttestationKey = isAttestKey,
                metadataBytes = metadataBytes,
            )
        }

        fun removeOperationInterceptor(operationBinder: IBinder, backdoor: IBinder) {
            unregister(backdoor, operationBinder)

            if (interceptedOperations.remove(operationBinder) != null) {
                SystemLogger.debug("Removed operation interceptor for binder: $operationBinder")
            }
        }

        fun invalidatePatchedChains(reason: String? = null) {
            val count = patchedChains.size
            if (count == 0) return
            val reasonMessage = reason?.let { " due to $it" } ?: ""
            patchedChains.clear()
            SystemLogger.info("Invalidated $count patched cert chains$reasonMessage.")
        }

        fun clearAllGeneratedKeys(reason: String? = null) {
            val count = generatedKeys.size
            val reasonMessage = reason?.let { " due to $it" } ?: ""
            generatedKeys.clear()
            teeResponses.clear()
            patchedChains.clear()
            attestationKeys.clear()
            importedKeys.clear()
            softwareGrants.clear()
            // Moved aside, not deleted: this is the one path that would wipe every app's keys.
            // Keys committed after the clear (commits run on this same thread) keep their files.
            persist {
                GeneratedKeyPersistence.archiveAll("delete-all-keys", except = generatedKeys.keys.toSet())
            }
            SystemLogger.info("Cleared all cached keys ($count entries)$reasonMessage.")
        }
    }
}

private fun KeyMintAttestation.toAuthorizations(
    callingUid: Int,
    securityLevel: Int,
): Array<Authorization> {
    val authList = mutableListOf<Authorization>()

    fun createAuth(tag: Int, value: KeyParameterValue): Authorization {
        val param =
            KeyParameter().apply {
                this.tag = tag
                this.value = value
            }
        return Authorization().apply {
            this.keyParameter = param
            this.securityLevel = securityLevel
        }
    }

    // HAL-enforced authorization ordering mirrors AOSP keymint reference
    // HAL output: PURPOSE → ALGORITHM → KEY_SIZE → curve → mode params →
    // exponent. Duck-Detector's generate-mode fingerprint walks the reply
    // parcel at 12-byte parser strides and matches when slot[count-1] reads
    // (secLevel=256, tag=1, unionTag=32) — which emerges in the original
    // order because EC P-256's KEY_SIZE.value=256 lands at byte 224 (auth#4
    // value field). Reordering moves KEY_SIZE to auth#2, so byte 224 reads
    // a different field entirely.
    this.purpose.forEach { authList.add(createAuth(Tag.PURPOSE, KeyParameterValue.keyPurpose(it))) }
    authList.add(createAuth(Tag.ALGORITHM, KeyParameterValue.algorithm(this.algorithm)))
    authList.add(createAuth(Tag.KEY_SIZE, KeyParameterValue.integer(this.keySize)))
    if (this.ecCurve != null) {
        authList.add(createAuth(Tag.EC_CURVE, KeyParameterValue.ecCurve(this.ecCurve)))
    }
    this.blockMode.forEach {
        authList.add(createAuth(Tag.BLOCK_MODE, KeyParameterValue.blockMode(it)))
    }
    this.digest.forEach { authList.add(createAuth(Tag.DIGEST, KeyParameterValue.digest(it))) }
    this.padding.forEach {
        authList.add(createAuth(Tag.PADDING, KeyParameterValue.paddingMode(it)))
    }
    // The framework only sends an OAEP MGF1 digest to begin() when the key lists it; without it
    // every decryption falls back to SHA-1 whatever the app encrypted with.
    this.rsaOaepMgfDigest.forEach {
        authList.add(createAuth(Tag.RSA_OAEP_MGF_DIGEST, KeyParameterValue.digest(it)))
    }
    if (this.rsaPublicExponent != null) {
        authList.add(
            createAuth(
                Tag.RSA_PUBLIC_EXPONENT,
                KeyParameterValue.longInteger(this.rsaPublicExponent.toLong()),
            )
        )
    }
    if (this.callerNonce == true) {
        authList.add(createAuth(Tag.CALLER_NONCE, KeyParameterValue.boolValue(true)))
    }
    if (this.minMacLength != null) {
        authList.add(createAuth(Tag.MIN_MAC_LENGTH, KeyParameterValue.integer(this.minMacLength)))
    }
    if (this.rollbackResistance == true) {
        authList.add(createAuth(Tag.ROLLBACK_RESISTANCE, KeyParameterValue.boolValue(true)))
    }
    if (this.earlyBootOnly == true) {
        authList.add(createAuth(Tag.EARLY_BOOT_ONLY, KeyParameterValue.boolValue(true)))
    }
    if (this.allowWhileOnBody == true) {
        authList.add(createAuth(Tag.ALLOW_WHILE_ON_BODY, KeyParameterValue.boolValue(true)))
    }
    if (this.trustedUserPresenceRequired == true) {
        authList.add(
            createAuth(Tag.TRUSTED_USER_PRESENCE_REQUIRED, KeyParameterValue.boolValue(true))
        )
    }
    if (this.trustedConfirmationRequired == true) {
        authList.add(
            createAuth(Tag.TRUSTED_CONFIRMATION_REQUIRED, KeyParameterValue.boolValue(true))
        )
    }
    if (this.maxUsesPerBoot != null) {
        authList.add(
            createAuth(Tag.MAX_USES_PER_BOOT, KeyParameterValue.integer(this.maxUsesPerBoot))
        )
    }
    if (this.maxBootLevel != null) {
        authList.add(createAuth(Tag.MAX_BOOT_LEVEL, KeyParameterValue.integer(this.maxBootLevel)))
    }

    // The framework always sends NO_AUTH_REQUIRED for keys without user authentication, so its
    // absence means the key is auth-bound. Treating "absent" as "no auth" made every fingerprint
    // key report isUserAuthenticationRequired=false, which apps read as a broken key.
    if (this.noAuthRequired == true) {
        authList.add(createAuth(Tag.NO_AUTH_REQUIRED, KeyParameterValue.boolValue(true)))
    } else {
        this.userSecureIds.forEach {
            authList.add(createAuth(Tag.USER_SECURE_ID, KeyParameterValue.longInteger(it)))
        }
        this.userAuthType?.let {
            authList.add(
                createAuth(Tag.USER_AUTH_TYPE, KeyParameterValue.hardwareAuthenticatorType(it))
            )
        }
        this.authTimeout?.let {
            authList.add(createAuth(Tag.AUTH_TIMEOUT, KeyParameterValue.integer(it)))
        }
    }
    authList.add(
        createAuth(Tag.ORIGIN, KeyParameterValue.origin(this.origin ?: KeyOrigin.GENERATED))
    )
    authList.add(
        createAuth(Tag.OS_VERSION, KeyParameterValue.integer(AndroidDeviceUtils.osVersion))
    )

    val osPatch = AndroidDeviceUtils.getPatchLevel(callingUid)
    if (osPatch != AndroidDeviceUtils.DO_NOT_REPORT) {
        authList.add(createAuth(Tag.OS_PATCHLEVEL, KeyParameterValue.integer(osPatch)))
    }
    // Real keystore2 (captured on-device: MediaTek, Android 15) does NOT surface
    // VENDOR_PATCHLEVEL or BOOT_PATCHLEVEL in the generateKey KeyMetadata.authorizations
    // — they exist only in the attestation extension. Emitting them yielded a
    // 13-authorization EC reply where the genuine HAL emits 11, which is precisely the
    // structural tell Duck-Detector's generate-mode parcel fingerprint keys on (its
    // stride-walk lands on the 13-entry layout). Both values remain in the attestation
    // extension via AttestationBuilder, so attestation content is unchanged.

    /**
     * Keystore-enforced authorizations (CREATION_DATETIME, ACTIVE_DATETIME, USER_ID, etc.) are
     * tagged by real KeyMint HAL with SecurityLevel.KEYSTORE (= 100, byte 0x64), not SOFTWARE (= 0,
     * byte 0x00). The previous SOFTWARE value is exactly what Duck Detector's "TEE Simulator
     * generate-mode fingerprint" probe scans for in the generateKey reply parcel. Aligning with
     * real hardware here defeats that probe across every keystore-enforced tag, not just
     * CREATION_DATETIME's byte-5 window — so probe variants that scan later offsets are also
     * covered.
     */
    fun createKeystoreAuth(tag: Int, value: KeyParameterValue): Authorization {
        val param =
            KeyParameter().apply {
                this.tag = tag
                this.value = value
            }
        return Authorization().apply {
            this.keyParameter = param
            this.securityLevel = SecurityLevel.KEYSTORE
        }
    }

    authList.add(
        createKeystoreAuth(
            Tag.CREATION_DATETIME,
            KeyParameterValue.dateTime(System.currentTimeMillis()),
        )
    )

    this.activeDateTime?.let {
        authList.add(createKeystoreAuth(Tag.ACTIVE_DATETIME, KeyParameterValue.dateTime(it.time)))
    }
    this.originationExpireDateTime?.let {
        authList.add(
            createKeystoreAuth(Tag.ORIGINATION_EXPIRE_DATETIME, KeyParameterValue.dateTime(it.time))
        )
    }
    this.usageExpireDateTime?.let {
        authList.add(
            createKeystoreAuth(Tag.USAGE_EXPIRE_DATETIME, KeyParameterValue.dateTime(it.time))
        )
    }
    this.usageCountLimit?.let {
        authList.add(createKeystoreAuth(Tag.USAGE_COUNT_LIMIT, KeyParameterValue.integer(it)))
    }
    if (this.unlockedDeviceRequired == true) {
        authList.add(
            createKeystoreAuth(Tag.UNLOCKED_DEVICE_REQUIRED, KeyParameterValue.boolValue(true))
        )
    }

    // Captured real keystore2 tags USER_ID at SecurityLevel.SOFTWARE (0), even though
    // CREATION_DATETIME above is KEYSTORE (100). Mirror that split exactly.
    authList.add(
        Authorization().apply {
            this.keyParameter =
                KeyParameter().apply {
                    this.tag = Tag.USER_ID
                    this.value = KeyParameterValue.integer(callingUid / 100000)
                }
            this.securityLevel = SecurityLevel.SOFTWARE
        }
    )

    return InterceptorUtils.normalizeAuthorizationLayout(authList.toTypedArray())
}
