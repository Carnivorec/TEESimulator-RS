package org.matrix.TEESimulator.config

import android.content.pm.IPackageManager
import android.os.Build
import android.os.FileObserver
import android.os.IBinder
import android.os.ServiceManager
import java.io.File
import java.io.IOException
import java.util.concurrent.ConcurrentHashMap
import org.matrix.TEESimulator.attestation.DeviceAttestationService
import org.matrix.TEESimulator.interception.keystore.shim.GeneratedKeyPersistence
import org.matrix.TEESimulator.interception.keystore.shim.KeyMintSecurityLevelInterceptor
import org.matrix.TEESimulator.logging.SystemLogger
import org.matrix.TEESimulator.pki.KeyBoxManager

/**
 * Manages application configuration, including which packages to process, what operation mode to
 * use, and custom security patch levels. It uses a FileObserver to dynamically reload settings when
 * configuration files change.
 */
object ConfigurationManager {

    /** Defines the processing mode for a given package. */
    enum class Mode {
        /** Automatically decide between GENERATE and PATCH based on TEE status. */
        AUTO,
        /** Patch the attestation of an existing certificate chain. */
        PATCH,
        /** Generate a new certificate chain from scratch. */
        GENERATE,
    }

    // --- Configuration Paths ---
    const val CONFIG_PATH = "/data/adb/tricky_store"
    private const val TARGET_PACKAGES_FILE = "target.txt"
    private const val PATCH_LEVEL_FILE = "security_patch.txt"
    private const val RELEASE_KEYS_FILE = "release_keys.txt"
    private const val DEFAULT_KEYBOX_FILE = "keybox.xml"
    private val configRoot = File(CONFIG_PATH)

    // --- In-Memory Configuration State ---
    @Volatile private var packageModes = mapOf<String, Mode>()
    @Volatile private var packageKeyboxes = mapOf<String, String>()
    @Volatile private var globalCustomPatchLevel: CustomPatchLevel? = null
    @Volatile private var packagePatchLevels = mapOf<String, CustomPatchLevel>()
    @Volatile private var keyReleaseRequestsReady = false

    // Cache for UID to package name resolution. Entries expire, so a uid reused by a newly
    // installed package does not keep the old package's configuration.
    private class CachedPackages(val packages: Array<String>, val loadedAtMs: Long)

    private val uidToPackagesCache = ConcurrentHashMap<Int, CachedPackages>()
    private const val UID_CACHE_TTL_MS = 60_000L
    private const val EMPTY_UID_CACHE_TTL_MS = 5_000L

    // System uids are shared by many packages (uid 1000 alone covers system_server, Settings and
    // dozens of vendor apps), so a target entry for any one of them would take over the keys of
    // the whole system. They are never targeted.
    private const val FIRST_APPLICATION_UID = 10000
    private val warnedSystemUids: MutableSet<Int> = ConcurrentHashMap.newKeySet()

    private fun isSystemUid(uid: Int): Boolean {
        if (uid % 100000 >= FIRST_APPLICATION_UID) return false
        if (warnedSystemUids.add(uid)) {
            val listed = getPackagesForUid(uid).filter { it in packageModes }
            if (listed.isNotEmpty())
                SystemLogger.warning(
                    "Ignoring target entries $listed: uid $uid is a shared system uid."
                )
        }
        return true
    }

    /** A config line without surrounding blanks or the UTF-8 byte order mark some editors add. */
    private fun cleanLine(line: String): String = line.trim().removePrefix("﻿").trim()

    /**
     * Initializes the configuration manager by loading all settings from disk and starting the file
     * observer to watch for changes.
     */
    fun initialize() {
        configRoot.mkdirs()
        SystemLogger.info("Configuration root is: ${configRoot.absolutePath}")

        // First, ensure the package manager service is running, as the TEE check depends on it.
        // This prevents a race condition on startup.
        SystemLogger.info("Waiting for PackageManagerService to be ready...")
        if (getPackageManager() == null) {
            SystemLogger.error(
                "PackageManagerService is not available. TEE check will likely fail."
            )
        } else {
            SystemLogger.info("PackageManagerService is ready.")
        }

        // Initial load of all configuration files.
        loadTargetPackages(File(configRoot, TARGET_PACKAGES_FILE))
        loadPatchLevelConfig(File(configRoot, PATCH_LEVEL_FILE))
        // Start watching for any subsequent file changes.
        ConfigObserver.startWatching()
        SystemLogger.info("Configuration initialized and file observer started.")
    }

    /**
     * Determines the keybox file to be used for a given UID. It maps the UID to its package(s) and
     * checks for a specific keybox mapping.
     *
     * @param uid The calling UID.
     * @return The name of the keybox file, or the default if none is specified.
     */
    fun getKeyboxFileForUid(uid: Int): String {
        val packages = getPackagesForUid(uid)
        return packages.firstNotNullOfOrNull { pkg -> packageKeyboxes[pkg] } ?: DEFAULT_KEYBOX_FILE
    }

    fun shouldPatch(uid: Int): Boolean {
        val mode = getPackageModeForUid(uid)
        return mode == Mode.PATCH || mode == Mode.AUTO
    }

    /** Determines if a new certificate needs to be generated for a given UID. */
    fun shouldGenerate(uid: Int): Boolean = getPackageModeForUid(uid) == Mode.GENERATE

    fun shouldSkipUid(uid: Int): Boolean = getPackageModeForUid(uid) == null

    fun isAutoMode(uid: Int): Boolean {
        if (isSystemUid(uid)) return false
        for (pkg in getPackagesForUid(uid)) {
            when (packageModes[pkg]) {
                Mode.GENERATE,
                Mode.PATCH -> return false
                Mode.AUTO -> return true
                null -> continue
            }
        }
        return false
    }

    private fun getPackageModeForUid(uid: Int): Mode? {
        if (isSystemUid(uid)) return null
        val packages = getPackagesForUid(uid)
        if (packages.isEmpty()) return null

        for (pkg in packages) {
            when (packageModes[pkg]) {
                Mode.GENERATE -> return Mode.GENERATE
                Mode.PATCH -> return Mode.PATCH
                Mode.AUTO ->
                    return if (DeviceAttestationService.isTeeAttesting) Mode.PATCH
                    else Mode.GENERATE
                null -> continue
            }
        }
        return null
    }

    /**
     * Retrieves the custom patch level configuration for a given UID. It first checks for a
     * package-specific override and falls back to the global configuration.
     *
     * @param uid The UID of the calling application.
     * @return The applicable [CustomPatchLevel], or null if no custom configuration exists.
     */
    fun getPatchLevelForUid(uid: Int): CustomPatchLevel? {
        val packages = getPackagesForUid(uid)
        // Find the first package-specific configuration for this UID.
        val packageSpecificPatchLevel =
            packages.firstNotNullOfOrNull { pkg -> packagePatchLevels[pkg] }
        return packageSpecificPatchLevel ?: globalCustomPatchLevel
    }

    /**
     * Loads and parses the `target.txt` file, which defines the processing mode and keybox file for
     * each package.
     */
    private fun loadTargetPackages(file: File) {
        if (!file.exists()) {
            SystemLogger.warning("Configuration file not found: ${file.absolutePath}")
            return
        }

        val newModes = mutableMapOf<String, Mode>()
        val newKeyboxes = mutableMapOf<String, String>()
        var currentKeybox = DEFAULT_KEYBOX_FILE
        val keyboxRegex = Regex("^\\[([a-zA-Z0-9_.-]+\\.xml)]$")

        try {
            file.readLines().forEach { line ->
                val trimmedLine = cleanLine(line)
                if (trimmedLine.isEmpty() || trimmedLine.startsWith("#")) return@forEach

                // Check if the line defines a new keybox scope.
                keyboxRegex.find(trimmedLine)?.let {
                    currentKeybox = it.groupValues[1]
                    SystemLogger.info("Switching to keybox context: $currentKeybox")
                    return@forEach
                }

                when {
                    // Suffix '!' means force GENERATE mode.
                    trimmedLine.endsWith("!") -> {
                        val pkg = trimmedLine.removeSuffix("!").trim()
                        newModes[pkg] = Mode.GENERATE
                        newKeyboxes[pkg] = currentKeybox
                    }
                    // Suffix '?' means force PATCH mode.
                    trimmedLine.endsWith("?") -> {
                        val pkg = trimmedLine.removeSuffix("?").trim()
                        newModes[pkg] = Mode.PATCH
                        newKeyboxes[pkg] = currentKeybox
                    }
                    else -> {
                        newModes[trimmedLine] = Mode.AUTO
                        newKeyboxes[trimmedLine] = currentKeybox
                    }
                }
            }

            // Atomically update the configuration maps.
            packageModes = newModes
            packageKeyboxes = newKeyboxes
            uidToPackagesCache.clear() // Invalidate cache as package settings have changed.
            SystemLogger.info("Successfully loaded ${newModes.size} package configurations.")
        } catch (e: Exception) {
            SystemLogger.error("Failed to load or parse ${file.name}", e)
        }
    }

    /**
     * Loads and parses the `security_patch.txt` file, which can define both global and per-package
     * security patch levels.
     */
    private fun loadPatchLevelConfig(file: File) {
        if (!file.exists()) {
            globalCustomPatchLevel = null
            packagePatchLevels = emptyMap()
            return
        }

        try {
            val newPackageLevels = mutableMapOf<String, CustomPatchLevel>()
            var currentContext = "" // Empty string for global context
            val contextLines = mutableMapOf<String, MutableList<String>>()
            val contextRegex = Regex("^\\[([a-zA-Z0-9_.-]+)]$")

            // First pass: group lines by context (global or package-specific).
            file.readLines().forEach { line ->
                val trimmedLine = cleanLine(line)
                if (trimmedLine.isEmpty() || trimmedLine.startsWith("#")) return@forEach

                contextRegex.find(trimmedLine)?.let { currentContext = it.groupValues[1] }
                    ?: run {
                        contextLines
                            .computeIfAbsent(currentContext) { mutableListOf() }
                            .add(trimmedLine)
                    }
            }

            // Helper function to parse a set of lines into a CustomPatchLevel object.
            fun parseLines(lines: List<String>?): CustomPatchLevel? {
                if (lines.isNullOrEmpty()) return null

                // Handle simple case: one line sets the patch level for all components.
                if (lines.size == 1 && '=' !in lines[0]) {
                    return CustomPatchLevel(
                        system = null,
                        vendor = null,
                        boot = null,
                        all = lines[0],
                    )
                }

                // Handle key-value pair configuration.
                val map =
                    lines
                        .mapNotNull {
                            val parts = it.split('=', limit = 2)
                            if (parts.size == 2) parts[0].trim().lowercase() to parts[1].trim()
                            else null
                        }
                        .toMap()

                val all = map["all"]
                return CustomPatchLevel(
                    system = map["system"] ?: all,
                    vendor = map["vendor"] ?: all,
                    boot = map["boot"] ?: all,
                    all = all,
                )
            }

            // Parse global and per-package configurations.
            var newGlobalLevel = parseLines(contextLines[""])
            // TrickyAddon writes Pixel bulletin dates for boot/vendor but system=prop
            // resolves to the real device prop — force boot/vendor through the same path
            // to prevent cross-component date mismatches on non-Pixel devices.
            if (newGlobalLevel?.system.equals("prop", ignoreCase = true)) {
                SystemLogger.info(
                    "system=prop: forcing boot/vendor to derive from device props (were: boot=${newGlobalLevel?.boot}, vendor=${newGlobalLevel?.vendor})"
                )
                newGlobalLevel = newGlobalLevel?.copy(boot = "prop", vendor = "prop")
            }
            contextLines.remove("") // Remove global context to iterate over packages next

            for ((pkg, lines) in contextLines) {
                parseLines(lines)?.let { newPackageLevels[pkg] = it }
            }

            // Atomically update the configuration state.
            globalCustomPatchLevel = newGlobalLevel
            packagePatchLevels = newPackageLevels

            SystemLogger.info(
                "Loaded custom security patch levels: global config exists=${newGlobalLevel != null}, " +
                    "${newPackageLevels.size} package-specific configs."
            )
        } catch (e: Exception) {
            SystemLogger.error("Failed to load or parse ${file.name}", e)
        }
    }

    /** Called after both security levels have finished restoring their software keys. */
    fun onPersistedKeysLoaded() {
        keyReleaseRequestsReady = true
        processKeyReleaseRequest()
    }

    private fun processKeyReleaseRequest() {
        if (!keyReleaseRequestsReady) return
        KeyMintSecurityLevelInterceptor.persist {
            val request = File(configRoot, RELEASE_KEYS_FILE)
            if (!request.exists()) return@persist
            try {
                val packages =
                    request.readLines().map(::cleanLine).filter {
                        it.isNotEmpty() && !it.startsWith("#")
                    }
                // A file manager creates the file empty before anything is typed into it; leave it
                // for the save that names a package rather than consume it.
                if (packages.isEmpty()) return@persist
                val releasedUids = mutableSetOf<Int>()
                val results =
                    packages.map { packageName ->
                        val result =
                            try {
                                releasePackageKeys(packageName, releasedUids)
                            } catch (e: Exception) {
                                "FAILED ${e.message ?: e.javaClass.simpleName}"
                            }
                        SystemLogger.info("$packageName\t$result")
                        "$packageName\t$result"
                    }
                val done = File(configRoot, "$RELEASE_KEYS_FILE.done")
                val temporary = File(configRoot, "$RELEASE_KEYS_FILE.done.tmp")
                temporary.writeText(results.joinToString("\n", postfix = "\n"))
                if (!temporary.renameTo(done))
                    throw IOException("Failed to rename $temporary to $done")
                if (!request.delete()) throw IOException("Failed to delete $request")
            } catch (e: Exception) {
                SystemLogger.error("Failed to process $RELEASE_KEYS_FILE", e)
            }
        }
    }

    private fun releasePackageKeys(packageName: String, releasedUids: MutableSet<Int>): String {
        val pm = getPackageManager() ?: return "FAILED package manager unavailable"
        val packageInfo =
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU)
                pm.getPackageInfo(packageName, 0L, 0)
            else pm.getPackageInfo(packageName, 0, 0)
        val uid = packageInfo?.applicationInfo?.uid ?: return "FAILED package not found"
        if (uid in releasedUids) return "OK uid=$uid already released in this request"
        if (isSystemUid(uid)) return "REFUSED uid=$uid system uid"
        if (!shouldSkipUid(uid)) return "REFUSED uid=$uid still in target"

        val label = "released-$uid"
        val directory = GeneratedKeyPersistence.archiveDir(label)
        val archived =
            KeyMintSecurityLevelInterceptor.releaseUidKeys(uid, label, directory) +
                GeneratedKeyPersistence.archiveUid(uid, directory)
        releasedUids.add(uid)
        val dir = if (archived > 0) " dir=${directory.absolutePath}" else ""
        val packages = getPackagesForUid(uid).joinToString(",")
        return "OK uid=$uid archived=$archived$dir packages=$packages"
    }

    /**
     * A FileObserver that monitors the configuration directory for changes and triggers reloads of
     * the relevant settings.
     */
    private object ConfigObserver :
        FileObserver(configRoot, CLOSE_WRITE or MOVED_TO or MOVED_FROM or DELETE) {
        override fun onEvent(event: Int, path: String?) {
            path ?: return
            // Other files here (.health_state, key backups) change all the time and are not ours.
            if (
                path != TARGET_PACKAGES_FILE && path != PATCH_LEVEL_FILE &&
                    path != RELEASE_KEYS_FILE && !path.endsWith(".xml")
            )
                return
            if (path == RELEASE_KEYS_FILE && (event and (CLOSE_WRITE or MOVED_TO)) == 0) return
            SystemLogger.info("Configuration file change detected: $path (event: $event)")

            // A file moved away is gone just like a deleted one: its settings stop applying.
            val removed = (event and (DELETE or MOVED_FROM)) != 0
            when (path) {
                RELEASE_KEYS_FILE -> processKeyReleaseRequest()
                TARGET_PACKAGES_FILE ->
                    if (removed) {
                        SystemLogger.warning("$TARGET_PACKAGES_FILE was removed; no app is targeted.")
                        packageModes = emptyMap()
                        packageKeyboxes = emptyMap()
                    } else loadTargetPackages(File(configRoot, path))
                // A missing file resets the patch levels.
                PATCH_LEVEL_FILE -> loadPatchLevelConfig(File(configRoot, path))
                // Any change to an XML file is assumed to be a keybox.
                // The cache in KeyBoxManager will handle reloading it on its next use.
                else ->
                    if (path.endsWith(".xml")) {
                        val file = File(configRoot, path)
                        SystemLogger.info(
                            "Keybox file $path may have changed. It will be reloaded on next access."
                        )
                        KeyBoxManager.invalidateCache(path)
                        if (Build.VERSION.SDK_INT > Build.VERSION_CODES.R) {
                            // Drop only the patched cert chains so the next
                            // attestation request re-signs with the new keybox.
                            // Do NOT drop generatedKeys — that would destroy
                            // every alias/private key in memory and on disk,
                            // logging users out of any app that pinned a
                            // persisted keystore alias.
                            org.matrix.TEESimulator.interception.keystore.shim
                                .KeyMintSecurityLevelInterceptor
                                .invalidatePatchedChains("updating $file")
                        }
                    }
            }
        }
    }

    // --- System Service Utilities ---

    private var iPackageManager: IPackageManager? = null
    private val pmDeathRecipient =
        object : IBinder.DeathRecipient {
            override fun binderDied() {
                (iPackageManager as? IBinder)?.unlinkToDeath(this, 0)
                iPackageManager = null
                // Packages may be reinstalled or uids reassigned while it restarts.
                uidToPackagesCache.clear()
                SystemLogger.warning("Package manager service died. Will try to reconnect.")
            }
        }

    /** Retrieves an instance of the IPackageManager service. */
    fun getPackageManager(): IPackageManager? {
        if (iPackageManager == null) {
            // Use a robust method to get the service binder.
            val binder = waitForSystemService("package") ?: return null
            binder.linkToDeath(pmDeathRecipient, 0)
            iPackageManager = IPackageManager.Stub.asInterface(binder)
        }
        return iPackageManager
    }

    fun checkSELinuxPermission(callingPid: Int, tclass: String, perm: String): Boolean {
        return try {
            val callerCtx =
                java.io.File("/proc/$callingPid/attr/current").readText().trim('\u0000', ' ', '\n')
            val selfCtx =
                java.io.File("/proc/self/attr/current").readText().trim('\u0000', ' ', '\n')
            android.os.SELinux.checkSELinuxAccess(callerCtx, selfCtx, tclass, perm)
        } catch (_: Exception) {
            false
        }
    }

    fun hasPermissionForUid(uid: Int, permission: String): Boolean {
        val userId = uid / 100000
        return getPackagesForUid(uid).any { pkg ->
            try {
                getPackageManager()?.checkPermission(permission, pkg, userId) == 0
            } catch (_: Exception) {
                false
            }
        }
    }

    fun getPackagesForUid(uid: Int): Array<String> {
        // Monotonic: a wall clock set back would keep stale entries alive indefinitely.
        val now = android.os.SystemClock.elapsedRealtime()
        uidToPackagesCache[uid]
            ?.takeIf {
                now - it.loadedAtMs <
                    if (it.packages.isEmpty()) EMPTY_UID_CACHE_TTL_MS else UID_CACHE_TTL_MS
            }
            ?.let {
                return it.packages
            }
        val pm = getPackageManager() ?: return emptyArray()
        val packages =
            try {
                pm.getPackagesForUid(uid) ?: emptyArray()
            } catch (e: Exception) {
                // A failed lookup is not cached: that would silently drop a targeted app from
                // interception until the next reboot.
                SystemLogger.warning("Failed to get packages for UID $uid", e)
                return emptyArray()
            }
        // An empty answer (isolated processes, a uid being installed) is kept only briefly.
        uidToPackagesCache[uid] = CachedPackages(packages, now)
        return packages
    }

    /** Waits for a system service to become available, with retries. */
    private fun waitForSystemService(name: String): IBinder? {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
            return ServiceManager.waitForService(name)
        }
        // Fallback for older Android versions.
        repeat(70) {
            val service = ServiceManager.getService(name)
            if (service != null) return service
            Thread.sleep(500)
        }
        SystemLogger.error("Failed to get system service after multiple retries: $name")
        return null
    }
}

/** Data class representing custom security patch level overrides. */
data class CustomPatchLevel(
    val system: String?,
    val vendor: String?,
    val boot: String?,
    val all: String?,
)
