#!/bin/bash
# End-to-end tests through the Lean kernel. Locally (default) this needs `lake build` in lean/.
# With PHYSVERIFY_LEAN=vm it holds a VM lease for its whole lifetime (if configured), runs the
# suite remotely, and releases the lease. Safe to run detached:
#   setsid nohup tools/run_lean_tests.sh > /tmp/physics-lean-tests.log 2>&1 < /dev/null &
cd "$(dirname "$0")/.." || exit 1
if [ "${PHYSVERIFY_LEAN:-local}" = vm ]; then
  [ -f tools/vm.local.sh ] && . tools/vm.local.sh
  if [ -n "$PHYSVERIFY_VM_LEASE" ]; then
    trap '$PHYSVERIFY_VM_LEASE release physics-tests' EXIT
    $PHYSVERIFY_VM_LEASE acquire physics-tests "physics: lean test suite"
  fi
  for i in $(seq 20); do
    gcloud compute ssh "$PHYSVERIFY_VM" --project="$PHYSVERIFY_VM_PROJECT" \
      --zone="$PHYSVERIFY_VM_ZONE" --quiet --command=true >/dev/null 2>&1 && break
    sleep 15
  done
  tools/vm.sh build 2
else
  (cd lean && lake build 2>&1 | tail -2)
fi
uv run pytest -q tests/test_lean.py --durations=10 "$@"
echo "PYTEST_EXIT=$?"
