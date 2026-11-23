#!/usr/bin/env bash
# Optional local-host adapter. Use only on the minimal /workspace Linux host
# where /root is absent and configuring a bwrap loopback interface is denied.
# CI and ordinary Linux machines run verify-comparator.sh directly.
set -euo pipefail
script_dir=$(cd "$(dirname "$0")" && pwd)
offline_root=$(mktemp -d)
trap 'rm -rf -- "$offline_root"' EXIT
export ORIGINAL_NETWORK_NAMESPACE="$(readlink /proc/self/ns/net)"
export COMPARATOR_BWRAP="$script_dir/bwrap-in-offline-namespace.py"
export COMPARATOR_NAMESPACE_FILE="$offline_root/netns"
mkdir -p .lake
unshare --user --map-root-user --net bash -eu -c '
  printf "%s\n%s\n" "$(readlink /proc/self/ns/net)" "$ORIGINAL_NETWORK_NAMESPACE" > "$COMPARATOR_NAMESPACE_FILE"
  exec bwrap --tmpfs / --ro-bind /usr /usr --ro-bind /etc /etc --ro-bind /opt /opt \
    --symlink usr/bin /bin --symlink usr/sbin /sbin \
    --symlink usr/lib /lib --symlink usr/lib64 /lib64 \
    --dir /root --dir /run/user --dir /home --dir /var/cache --dir /var/tmp --dir /var/lib \
    --ro-bind "$COMPARATOR_NAMESPACE_FILE" /run/comparator-namespace \
    --tmpfs /tmp --dev /dev --proc /proc \
    --ro-bind /workspace /workspace --bind "$PWD/.lake" "$PWD/.lake" \
    --chdir "$PWD" -- "$@"
' -- "$@"
