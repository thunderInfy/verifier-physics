#!/bin/bash
# Optional: check Lean certificates on a remote GCP machine instead of locally.
# Configure with environment variables (or put them in tools/vm.local.sh, which is git-ignored):
#   PHYSVERIFY_VM            instance name
#   PHYSVERIFY_VM_PROJECT    GCP project id
#   PHYSVERIFY_VM_ZONE       zone, e.g. us-central1-a
#   PHYSVERIFY_VM_LEASE      optional lease script: `$LEASE acquire|release NAME "what"`
# Then run with PHYSVERIFY_LEAN=vm.
#
#   tools/vm.sh lease          hold a lease named "physics" (background holder)
#   tools/vm.sh release        drop it
#   tools/vm.sh sync           copy lean/ (sources only) to ~/physics-lean on the VM
#   tools/vm.sh build [N]      sync + lake exe cache get + lake build (last N lines)
#   tools/vm.sh lean FILE [T]  copy FILE into the project and run `lake env lean` on it
set -e
HERE=$(cd "$(dirname "$0")/.." && pwd)
[ -f "$HERE/tools/vm.local.sh" ] && . "$HERE/tools/vm.local.sh"
: "${PHYSVERIFY_VM:?set PHYSVERIFY_VM (see tools/vm.sh)}"
: "${PHYSVERIFY_VM_PROJECT:?set PHYSVERIFY_VM_PROJECT}"
: "${PHYSVERIFY_VM_ZONE:?set PHYSVERIFY_VM_ZONE}"
GC=(--project="$PHYSVERIFY_VM_PROJECT" --zone="$PHYSVERIFY_VM_ZONE" --quiet)
LEASE=${PHYSVERIFY_VM_LEASE:-}
REMOTE=physics-lean
ssh_() { gcloud compute ssh "$PHYSVERIFY_VM" "${GC[@]}" --command="$1"; }

case "$1" in
  lease)
    [ -n "$LEASE" ] || { echo "no PHYSVERIFY_VM_LEASE configured"; exit 0; }
    $LEASE list | grep -q '^physics:' && { echo "lease already held"; exit 0; }
    setsid nohup bash -c "$LEASE acquire physics 'physics verifier'; exec sleep 43200" \
      > /tmp/physics-lease.log 2>&1 < /dev/null &
    sleep 5; cat /tmp/physics-lease.log ;;
  release)
    [ -n "$LEASE" ] || exit 0
    pkill -f "acquire physics 'physics verifier'" 2>/dev/null || true
    $LEASE release physics ;;
  sync)
    tar czf /tmp/physics-lean.tgz -C "$HERE/lean" --exclude=.lake --exclude=build_certs .
    gcloud compute scp "${GC[@]}" /tmp/physics-lean.tgz "$PHYSVERIFY_VM":~/ >/dev/null
    ssh_ "mkdir -p ~/$REMOTE && tar xzf ~/physics-lean.tgz -C ~/$REMOTE && rm ~/physics-lean.tgz" ;;
  build)
    "$0" sync
    ssh_ "export PATH=\$HOME/.elan/bin:\$PATH; cd ~/$REMOTE && (test -d .lake/packages/mathlib || lake exe cache get >/dev/null 2>&1 || lake exe cache get) && lake build 2>&1 | tail -${2:-60}" ;;
  lean)
    f=$(basename "$2")
    gcloud compute scp "${GC[@]}" "$2" "$PHYSVERIFY_VM:~/$REMOTE/$f" >/dev/null
    ssh_ "export PATH=\$HOME/.elan/bin:\$PATH; cd ~/$REMOTE && timeout ${3:-300} lake env lean $f 2>&1; echo \"EXIT=\$?\"; rm -f $f" ;;
  *) echo "usage: tools/vm.sh lease|release|sync|build|lean FILE"; exit 1 ;;
esac
