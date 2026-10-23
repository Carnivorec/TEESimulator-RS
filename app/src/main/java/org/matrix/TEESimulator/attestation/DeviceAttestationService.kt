package org.matrix.TEESimulator.attestation

import android.annotation.SuppressLint
import android.security.KeyStoreException
import android.security.keystore.KeyGenParameterSpec
import android.security.keystore.KeyProperties
import java.security.KeyPairGenerator
import java.security.KeyStore
import java.security.SecureRandom
import java.security.cert.X509Certificate
import java.security.spec.ECGenParameterSpec
import java.security.spec.RSAKeyGenParameterSpec
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicBoolean
import org.bouncycastle.asn1.ASN1Integer
import org.bouncycastle.asn1.ASN1ObjectIdentifier
import org.bouncycastle.asn1.ASN1OctetString
import org.bouncycastle.asn1.ASN1Sequence
import org.bouncycastle.asn1.ASN1TaggedObject
import org.bouncycastle.asn1.x509.Extension
import org.bouncycastle.cert.X509CertificateHolder
import org.matrix.TEESimulator.logging.SystemLogger
import org.matrix.TEESimulator.util.AndroidDeviceUtils
import org.matrix.TEESimulator.util.toHex

/**
 * The ASN.1 Object Identifier for the Key Attestation extension in Android. This is defined in the
 * Android Keystore documentation.
 */
val ATTESTATION_OID: ASN1ObjectIdentifier = ASN1ObjectIdentifier("1.3.6.1.4.1.11129.2.1.17")

/**
 * A service to interact with the device's Trusted Execution Environment (TEE). It provides
 * functionality to check if the TEE is functional and to extract key attestation data from a
 * genuinely generated certificate.
 */
@SuppressLint("PrivateApi")
object DeviceAttestationService {

    /**
     * Holds key data extracted from a genuine device attestation. This data can be used as a
     * baseline for creating simulated attestations.
     *
     * @property verifiedBootKey The verified boot public key digest from the root of trust.
     * @property verifiedBootHash The verified boot hash from the root of trust.
     * @property attestVersion The attestation version (e.g., 400 for KeyMint 4.0).
     * @property keymasterVersion The Keymaster or KeyMint HAL version.
     * @property osVersion The Android OS version integer.
     * @property osPatchLevel The Android security patch level (e.g., 202511).
     * @property vendorPatchLevel The vendor-specific security patch level.
     * @property bootPatchLevel The bootloader's security patch level.
     */
    data class AttestationData(
        val moduleHash: ByteArray?,
        val verifiedBootKey: ByteArray?,
        val verifiedBootHash: ByteArray?,
        val attestVersion: Int?,
        val keymasterVersion: Int?,
        val osVersion: Int?,
        val osPatchLevel: Int?,
        val vendorPatchLevel: Int?,
        val bootPatchLevel: Int?,
    )

    // A unique alias for the key used to perform the TEE functionality check.
    private const val TEE_CHECK_KEY_ALIAS = "TEESimulator_AttestationCheck"

    // Alias of the key that probes the TEE without attestation, when the attested probe failed.
    private const val TEE_PLAIN_CHECK_KEY_ALIAS = "TEESimulator_TeeCheck"
    private const val TEE_REPROBE_INTERVAL_MS = 30_000L

    @Volatile private var teeVerdict: Boolean? = null
    @Volatile private var teeVerdictAtMs = 0L
    @Volatile private var lastTeeProbeMs = 0L

    /**
     * Before API 33 a keystore failure cannot be told transient or permanent, so every one counts
     * as permanent (see [isAttestationUnavailable]): the software fallback starts at once. Such a
     * negative verdict is only a guess, though, and a hardware hiccup must not pin it until the next
     * reboot, so it is probed again once this long has passed. From API 33 on a negative verdict is
     * definitive and kept.
     */
    private const val GUESSED_NEGATIVE_TTL_MS = 5 * 60_000L

    private val canTellTransient: Boolean
        get() = android.os.Build.VERSION.SDK_INT >= 33

    /** Whether a negative verdict reached at [atMs] was a guess that is due for a new probe. */
    private fun isGuessedNegativeExpired(atMs: Long, now: Long): Boolean =
        !canTellTransient && now - atMs >= GUESSED_NEGATIVE_TTL_MS
    private val teeProbeInFlight = AtomicBoolean(false)

    /**
     * Whether the device's TEE can generate keys. Every key of every targeted app is forged while
     * this is false, symmetric ones included, so only a definitive answer is cached: a working
     * TEE, or a permanent keystore failure. An inconclusive probe (early in boot, attestation keys not provisioned
     * yet) reports a working TEE and is retried after [TEE_REPROBE_INTERVAL_MS]; it used to stick
     * as "no TEE" for the whole boot.
     */
    val isTeeFunctional: Boolean
        get() {
            val now = android.os.SystemClock.elapsedRealtime()
            teeVerdict?.let { if (it || !isGuessedNegativeExpired(teeVerdictAtMs, now)) return it }
            if (
                (lastTeeProbeMs == 0L || now - lastTeeProbeMs >= TEE_REPROBE_INTERVAL_MS) &&
                    teeProbeInFlight.compareAndSet(false, true)
            ) {
                try {
                    // As for the attestation verdicts: the verdict is only written while holding
                    // the flag, so recheck it in case another probe settled it meanwhile.
                    val standing = teeVerdict
                    if (
                        standing == null ||
                            (!standing && isGuessedNegativeExpired(teeVerdictAtMs, now))
                    ) {
                        lastTeeProbeMs = now
                        // Its attested probe settles [isTeeAttesting] too, which waits for it.
                        teeVerdict = synchronized(attestProbeLock) { checkTeeFunctionality() }
                        teeVerdictAtMs = now
                    }
                } finally {
                    teeProbeInFlight.set(false)
                }
            }
            return teeVerdict ?: true
        }

    @Volatile private var teeAttests = false
    @Volatile private var lastAttestedProbeMs = 0L
    private val attestProbeLock = Any()

    /**
     * Whether the TEE can attest a key, which is what AUTO mode decides on. A TEE can work while
     * attestation does not (attestation keys revoked, broken or not provisioned yet), and AUTO
     * PATCHing every attested key of every targeted app then fails them all; while this is false
     * AUTO forges as GENERATE does, symmetric keys still going to the working TEE. A failed attested
     * probe is retried after [TEE_REPROBE_INTERVAL_MS] in case attestation becomes available.
     *
     * Callers wait for a probe in flight rather than read the default: a request answered "no"
     * while a working TEE is still being probed would be forged, and its key stays forged.
     */
    val isTeeAttesting: Boolean
        get() {
            if (teeAttests) return true
            synchronized(attestProbeLock) {
                if (teeAttests || !isTeeFunctional) return teeAttests
                val now = android.os.SystemClock.elapsedRealtime()
                if (
                    lastAttestedProbeMs == 0L ||
                        now - lastAttestedProbeMs >= TEE_REPROBE_INTERVAL_MS
                ) {
                    lastAttestedProbeMs = now
                    // The key is kept, as after the first check, for [CachedAttestationData].
                    runCatching { generateTeeCheckKey(TEE_CHECK_KEY_ALIAS, attested = true) }
                        .onSuccess {
                            teeAttests = true
                            recordTeeCheck("TEE attestation is available now.", null)
                        }
                }
                return teeAttests
            }
        }

    // Per (algorithm, security-level) attestation-capability verdicts, keyed by probe-key alias.
    // A device may attest one algorithm or security level yet lack a provisioned attestation key
    // for another (e.g. a TEE that attests RSA over a StrongBox that cannot), so each pair is
    // probed and cached on its own.
    private data class ProbeSpec(
        val algorithm: String,
        val strongBox: Boolean,
        val keyAlias: String,
    )

    private val rsaTeeProbe =
        ProbeSpec(KeyProperties.KEY_ALGORITHM_RSA, false, "TEESimulator_RsaAttestCheck")
    private val rsaStrongBoxProbe =
        ProbeSpec(KeyProperties.KEY_ALGORITHM_RSA, true, "TEESimulator_RsaAttestCheckSb")
    private val ecTeeProbe =
        ProbeSpec(KeyProperties.KEY_ALGORITHM_EC, false, "TEESimulator_EcAttestCheck")
    private val ecStrongBoxProbe =
        ProbeSpec(KeyProperties.KEY_ALGORITHM_EC, true, "TEESimulator_EcAttestCheckSb")

    private val attestableVerdicts = ConcurrentHashMap<String, Boolean>()
    private val attestableVerdictAtMs = ConcurrentHashMap<String, Long>()
    private val attestProbesInFlight = ConcurrentHashMap<String, AtomicBoolean>()

    /**
     * Whether the real hardware can attest an RSA key at the requested security level. AUTO dispatch
     * reads this to forge RSA attestation only where the hardware genuinely cannot serve it.
     *
     * Only a definitive verdict is cached: a successful probe, or a permanent keystore failure. A
     * transient or unrecognized failure leaves the verdict unset and reports attestable, so dispatch
     * PATCHes the genuine chain and re-probes next read — a one-off keystore hiccup can never freeze
     * the device into forging an attestation it could serve.
     */
    fun isRsaAttestable(strongBox: Boolean): Boolean =
        isHardwareAttestable(if (strongBox) rsaStrongBoxProbe else rsaTeeProbe)

    /** Whether the real hardware can attest an EC key at the requested security level. */
    fun isEcAttestable(strongBox: Boolean): Boolean =
        isHardwareAttestable(if (strongBox) ecStrongBoxProbe else ecTeeProbe)

    /** The cached verdict for [alias], unless it is a guess that has expired. */
    private fun standingAttestableVerdict(alias: String, now: Long): Boolean? =
        attestableVerdicts[alias]?.takeIf {
            it || !isGuessedNegativeExpired(attestableVerdictAtMs[alias] ?: 0L, now)
        }

    private fun isHardwareAttestable(probe: ProbeSpec): Boolean {
        val now = android.os.SystemClock.elapsedRealtime()
        standingAttestableVerdict(probe.keyAlias, now)?.let { return it }
        val probeInFlight =
            attestProbesInFlight.computeIfAbsent(probe.keyAlias) { AtomicBoolean(false) }
        if (probeInFlight.compareAndSet(false, true)) {
            try {
                // Verdicts are only written while holding the flag. Another probe may have
                // settled this one between the read above and taking it; if not, what is cached
                // now is nothing or an expired guess, and only that may be replaced.
                if (standingAttestableVerdict(probe.keyAlias, now) == null) {
                    val verdict = probeAttestability(probe)
                    if (verdict != null) {
                        attestableVerdicts[probe.keyAlias] = verdict
                        attestableVerdictAtMs[probe.keyAlias] = now
                    } else {
                        // Inconclusive: the expired guess no longer stands; capable is the default.
                        attestableVerdicts.remove(probe.keyAlias)
                    }
                }
            } finally {
                probeInFlight.set(false)
            }
        }
        return attestableVerdicts[probe.keyAlias] ?: true
    }

    @Volatile private var cachedAttestationData: AttestationData? = null
    @Volatile private var lastAttestationFetchMs = 0L

    /**
     * Attestation data parsed from a genuinely generated certificate, or null while none could be
     * obtained (no working TEE, attestation not available yet, parsing failed). Only a result is
     * cached; a failed fetch is retried after [TEE_REPROBE_INTERVAL_MS].
     */
    val CachedAttestationData: AttestationData?
        get() {
            cachedAttestationData?.let { return it }
            val now = android.os.SystemClock.elapsedRealtime()
            synchronized(this) {
                cachedAttestationData?.let { return it }
                if (lastAttestationFetchMs != 0L && now - lastAttestationFetchMs < TEE_REPROBE_INTERVAL_MS)
                    return null
                lastAttestationFetchMs = now
                cachedAttestationData = fetchAttestationData()
            }
            return cachedAttestationData
        }

    private fun generateTeeCheckKey(alias: String, attested: Boolean) {
        val keyPairGenerator =
            KeyPairGenerator.getInstance(KeyProperties.KEY_ALGORITHM_EC, "AndroidKeyStore")
        val builder =
            KeyGenParameterSpec.Builder(alias, KeyProperties.PURPOSE_SIGN)
                .setAlgorithmParameterSpec(ECGenParameterSpec("secp256r1"))
                .setDigests(KeyProperties.DIGEST_SHA256)
        // A random challenge is required for attestation.
        if (attested)
            builder.setAttestationChallenge(ByteArray(16).apply { SecureRandom().nextBytes(this) })
        keyPairGenerator.initialize(builder.build())
        keyPairGenerator.generateKeyPair()
    }

    /**
     * Checks whether the TEE works. An attested key is tried first, as its certificate also feeds
     * [CachedAttestationData]. Attestation can fail on a working TEE (remotely provisioned keys
     * not available yet early in boot), so a failure is retried with a plain key, which needs no
     * attestation key at all.
     *
     * @return true if the TEE generated a key, false on a permanent keystore failure, null if the
     *   result is inconclusive and the check should run again later.
     */
    private fun checkTeeFunctionality(): Boolean? {
        SystemLogger.info("Performing TEE functionality check...")
        try {
            lastAttestedProbeMs = android.os.SystemClock.elapsedRealtime()
            generateTeeCheckKey(TEE_CHECK_KEY_ALIAS, attested = true)
            teeAttests = true
            recordTeeCheck("TEE functionality check successful.", null)
            return true
        } catch (e: Exception) {
            recordTeeCheck("Attested TEE check failed; retrying without attestation.", e)
        }
        return try {
            generateTeeCheckKey(TEE_PLAIN_CHECK_KEY_ALIAS, attested = false)
            recordTeeCheck("TEE works; attestation is not available, AUTO forges for now.", null)
            true
        } catch (e: Exception) {
            // The same transient/permanent line the attestation probes draw.
            val permanent = isAttestationUnavailable(e)
            recordTeeCheck(
                if (permanent) "TEE functionality check failed permanently."
                else "TEE functionality check inconclusive; will retry.",
                e,
            )
            if (permanent) false else null
        } finally {
            deleteProbeKey(TEE_PLAIN_CHECK_KEY_ALIAS)
        }
    }

    private val teeCheckLog = java.io.File("/data/adb/tricky_store/logs/tee_check.log")
    private const val TEE_CHECK_LOG_MAX_BYTES = 64 * 1024L

    /**
     * Logs a TEE check result, and also appends it to a small file of its own: whether AUTO mode
     * forges is decided here once per boot, and logcat has rotated that line away by the time
     * anyone looks.
     */
    private fun recordTeeCheck(message: String, error: Throwable?) {
        if (error == null) SystemLogger.info(message) else SystemLogger.warning(message, error)
        runCatching {
            // The logs directory is otherwise made by libcertgen's logger, which is exactly what
            // may have failed to load when this record is needed.
            teeCheckLog.parentFile?.mkdirs()
            if (teeCheckLog.length() > TEE_CHECK_LOG_MAX_BYTES)
                teeCheckLog.renameTo(java.io.File(teeCheckLog.path + ".old"))
            val time = java.text.SimpleDateFormat("yyyy-MM-dd HH:mm:ss", java.util.Locale.US)
                .format(java.util.Date())
            val cause = error?.let { " (${it.javaClass.simpleName}: ${it.message})" } ?: ""
            teeCheckLog.appendText("$time $message$cause\n")
        }
    }

    /**
     * Probes whether the real hardware can attest a key matching [probe] by generating one with an
     * attestation challenge at the probe's algorithm and security level. Mirrors
     * [checkTeeFunctionality]; the request runs as the module UID, so it is skipped by interception
     * and reaches genuine hardware rather than the forge path.
     *
     * @return `true` if attestation succeeded, `false` only on a confirmed attestation-keys-
     *   unavailable failure, or `null` on a transient or unrecognized failure where the caller
     *   fails open and re-probes.
     */
    private fun probeAttestability(probe: ProbeSpec): Boolean? {
        val label = "${probe.algorithm} attestation (strongBox=${probe.strongBox})"
        SystemLogger.info("Performing $label capability check...")
        return try {
            val keyPairGenerator =
                KeyPairGenerator.getInstance(probe.algorithm, "AndroidKeyStore")

            val challenge = ByteArray(16).apply { SecureRandom().nextBytes(this) }

            val builder =
                KeyGenParameterSpec.Builder(probe.keyAlias, KeyProperties.PURPOSE_SIGN)
                    .setDigests(KeyProperties.DIGEST_SHA256)
                    .setAttestationChallenge(challenge)
                    .setIsStrongBoxBacked(probe.strongBox)
            if (probe.algorithm == KeyProperties.KEY_ALGORITHM_RSA) {
                builder
                    .setAlgorithmParameterSpec(RSAKeyGenParameterSpec(2048, RSAKeyGenParameterSpec.F4))
                    .setSignaturePaddings(KeyProperties.SIGNATURE_PADDING_RSA_PKCS1)
            } else {
                builder.setAlgorithmParameterSpec(ECGenParameterSpec("secp256r1"))
            }

            keyPairGenerator.initialize(builder.build())
            keyPairGenerator.generateKeyPair()

            SystemLogger.info("$label capability check successful.")
            true
        } catch (e: Exception) {
            if (isAttestationUnavailable(e)) {
                SystemLogger.info("$label unsupported by hardware; AUTO will forge attestation.")
                false
            } else {
                SystemLogger.warning(
                    "$label capability check failed transiently; treating as capable.",
                    e,
                )
                null
            }
        } finally {
            deleteProbeKey(probe.keyAlias)
        }
    }

    /**
     * Whether [error] definitively means the hardware cannot attest the probed key: a permanent
     * [KeyStoreException] from the keystore. Transient failures and non-keystore errors return
     * `false`, so the caller fails open and re-probes rather than caching a guess. The probe runs a
     * fixed, valid spec as root, so its only permanent keystore failure mode is missing attestation
     * support; [KeyStoreException.isTransientFailure] draws the transient/permanent line.
     */
    private fun isAttestationUnavailable(error: Throwable): Boolean {
        // isTransientFailure arrived in API 33; calling it earlier throws NoSuchMethodError, which
        // no `catch (Exception)` stops. Without it any keystore failure counts as permanent, as
        // every failure did before the check learned to retry: treating none as permanent would
        // keep a broken TEE in use forever, with no software fallback. Such a verdict expires
        // after GUESSED_NEGATIVE_TTL_MS.
        var cause: Throwable? = error
        while (cause != null) {
            val keyStoreError = cause as? KeyStoreException
            if (keyStoreError != null) return !canTellTransient || !keyStoreError.isTransientFailure
            cause = cause.cause
        }
        return false
    }

    private fun deleteProbeKey(keyAlias: String) {
        try {
            KeyStore.getInstance("AndroidKeyStore").apply { load(null) }.deleteEntry(keyAlias)
        } catch (e: Exception) {
            SystemLogger.warning("Failed to delete attestation probe key.", e)
        }
    }

    /**
     * Retrieves the attestation certificate generated during the TEE check. The key entry is
     * deleted after retrieval to clean up.
     *
     * @return The leaf `X509Certificate` containing the attestation, or `null` if unavailable.
     */
    private fun getAttestationCertificate(): X509Certificate? {
        if (!isTeeFunctional) return null

        return try {
            val keyStore = KeyStore.getInstance("AndroidKeyStore").apply { load(null) }
            // The TEE check leaves its attested key behind; when that attempt failed or the key
            // was already consumed, make a new one.
            if (!keyStore.containsAlias(TEE_CHECK_KEY_ALIAS))
                generateTeeCheckKey(TEE_CHECK_KEY_ALIAS, attested = true)
            val certChain = keyStore.getCertificateChain(TEE_CHECK_KEY_ALIAS)
            if (certChain.isNullOrEmpty()) {
                SystemLogger.warning("Could not retrieve certificate chain for TEE check key.")
                null
            } else {
                // Clean up the key from the keystore.
                keyStore.deleteEntry(TEE_CHECK_KEY_ALIAS)
                certChain[0] as X509Certificate
            }
        } catch (e: Exception) {
            SystemLogger.error("Error retrieving attestation certificate.", e)
            null
        }
    }

    /**
     * Fetches and parses the attestation data from the certificate's extension.
     *
     * @return An `AttestationData` object, or `null` if the process fails.
     */
    private fun fetchAttestationData(): AttestationData? {
        val leafCert = getAttestationCertificate() ?: return null

        try {
            val leafHolder = X509CertificateHolder(leafCert.encoded)
            val extension: Extension =
                leafHolder.getExtension(ATTESTATION_OID)
                    ?: return null // No attestation extension found.

            // The extension's value is an ASN.1 sequence.
            val keyDescriptionSeq = ASN1Sequence.getInstance(extension.extnValue.octets)
            SystemLogger.verbose {
                val formattedString =
                    keyDescriptionSeq.joinToString(separator = ", ") {
                        AttestationPatcher.formatAsn1Primitive(it)
                    }
                "Cached attestation data: $formattedString"
            }
            val fields = keyDescriptionSeq.toArray()

            val deviceAttestVersion =
                ASN1Integer.getInstance(
                        fields[AttestationConstants.KEY_DESCRIPTION_ATTESTATION_VERSION_INDEX]
                    )
                    .positiveValue
                    .toInt()
            // The device KeyMint HAL can report a version below its OS's AOSP value (100 on an A16
            // where BAKLAVA mandates 400); cache the AOSP value so the forge matches an updated device.
            val attestVersion = AndroidDeviceUtils.aospAttestVersion ?: deviceAttestVersion
            val keymasterVersion =
                ASN1Integer.getInstance(
                        fields[AttestationConstants.KEY_DESCRIPTION_KEYMINT_VERSION_INDEX]
                    )
                    .positiveValue
                    .toInt()

            var moduleHash: ByteArray? = null
            var verifiedBootKey: ByteArray? = null
            var verifiedBootHash: ByteArray? = null
            var osVersion: Int? = null
            var osPatchLevel: Int? = null
            var vendorPatchLevel: Int? = null
            var bootPatchLevel: Int? = null

            val softwareEnforced =
                ASN1Sequence.getInstance(
                    fields[AttestationConstants.KEY_DESCRIPTION_SOFTWARE_ENFORCED_INDEX]
                )
            moduleHash =
                softwareEnforced
                    .toArray()
                    .firstOrNull {
                        (it as? ASN1TaggedObject)?.tagNo == AttestationConstants.TAG_MODULE_HASH
                    }
                    ?.let {
                        ASN1OctetString.getInstance((it as ASN1TaggedObject).baseObject).octets
                    }

            val teeEnforced =
                ASN1Sequence.getInstance(
                    fields[AttestationConstants.KEY_DESCRIPTION_TEE_ENFORCED_INDEX]
                )
            teeEnforced.forEach { element ->
                val tagged = element as ASN1TaggedObject
                when (tagged.tagNo) {
                    AttestationConstants.TAG_ROOT_OF_TRUST -> {
                        val rotSeq = ASN1Sequence.getInstance(tagged.baseObject.toASN1Primitive())
                        if (rotSeq.size() >= 4) {
                            verifiedBootKey =
                                ASN1OctetString.getInstance(
                                        rotSeq.getObjectAt(
                                            AttestationConstants
                                                .ROOT_OF_TRUST_VERIFIED_BOOT_KEY_INDEX
                                        )
                                    )
                                    .octets
                            verifiedBootHash =
                                ASN1OctetString.getInstance(
                                        rotSeq.getObjectAt(
                                            AttestationConstants
                                                .ROOT_OF_TRUST_VERIFIED_BOOT_HASH_INDEX
                                        )
                                    )
                                    .octets
                        }
                    }
                    AttestationConstants.TAG_OS_VERSION -> {
                        osVersion =
                            ASN1Integer.getInstance(tagged.baseObject.toASN1Primitive())
                                .positiveValue
                                .toInt()
                    }
                    AttestationConstants.TAG_OS_PATCHLEVEL -> {
                        osPatchLevel =
                            ASN1Integer.getInstance(tagged.baseObject.toASN1Primitive())
                                .positiveValue
                                .toInt()
                    }
                    AttestationConstants.TAG_VENDOR_PATCHLEVEL -> {
                        vendorPatchLevel =
                            ASN1Integer.getInstance(tagged.baseObject.toASN1Primitive())
                                .positiveValue
                                .toInt()
                    }
                    AttestationConstants.TAG_BOOT_PATCHLEVEL -> {
                        bootPatchLevel =
                            ASN1Integer.getInstance(tagged.baseObject.toASN1Primitive())
                                .positiveValue
                                .toInt()
                    }
                }
            }

            if (verifiedBootKey?.all { it == 0.toByte() } == true) {
                verifiedBootKey = null
            }

            if (verifiedBootHash?.all { it == 0.toByte() } == true) {
                verifiedBootHash = null
            }

            SystemLogger.info(
                "Successfully extracted attestation data: version=$deviceAttestVersion, osVersion=$osVersion, osPatch=$osPatchLevel, vendorPatch=$vendorPatchLevel, bootPatch=$bootPatchLevel, moduleHash=${moduleHash?.toHex()}, bootKey=${verifiedBootKey?.toHex()}, bootHash=${verifiedBootHash?.toHex()}"
            )
            return AttestationData(
                moduleHash,
                verifiedBootKey,
                verifiedBootHash,
                attestVersion,
                keymasterVersion,
                osVersion,
                osPatchLevel,
                vendorPatchLevel,
                bootPatchLevel,
            )
        } catch (e: Exception) {
            SystemLogger.error("Failed to parse attestation data from certificate.", e)
            return null
        }
    }
}
