#!/system/bin/sh
MODDIR=${0%/*}
CONFIG_DIR=/data/adb/tricky_store

# Kill daemon and supervisor
for pid in $(pidof TEESimulator) $(pidof supervisor) $(pidof daemon); do
    kill -9 "$pid" 2>/dev/null
done

# Generated keys and the boot identity are user data: apps (banking, fingerprint unlock) bind
# their credentials to them. Keep them so a reinstall picks them up again. To wipe them, use the
# module action, which moves them to /data/adb/tricky_store_backup instead of deleting.
rm -f "$CONFIG_DIR/tee_status.txt"
# security_patch.txt may hold the user's own patch-level overrides; keep it like target.txt.
rm -f "$CONFIG_DIR/security_patch.txt.next" "$CONFIG_DIR/last_bulletin_fetch.json"

# Debug diagnostics live on external storage; remove them on uninstall.
rm -rf /data/media/0/TEESimulator
