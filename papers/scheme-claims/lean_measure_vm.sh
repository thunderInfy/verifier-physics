#!/usr/bin/env bash
# Usage (on the Lean machine, from lean/ of a checkout of the measured commit):
#   lean_measure_vm.sh JOBS RESULTS [LIMIT_S RETRY_S PARALLEL]
#
# The whole measured run of measure_lean.py, resumable (each step leaves RESULTS/<step>.done; a rerun skips
# what is done, and lean_run_jobs.sh resumes inside a step):
#   host.json   the machine (GCE machine type, CPUs, RAM) and the Lean and Mathlib versions in use
#   build       the Mathlib cache and `lake build` of PhysVerify, so each job only imports
#   jobs        every JOBS/<sha>.lean at LIMIT_S, PARALLEL at a time (lean_run_jobs.sh) into RESULTS
#   retry       the jobs that hit LIMIT_S, once more at RETRY_S, one at a time, into RESULTS_retry
#   registry    JOBS/../registry.lean (`#print axioms` of the registry's meaning theorems) into RESULTS
# Then copy RESULTS and RESULTS_retry back and run `measure_lean.py ingest` on each (the retry with
# --retry --parallel 1) and `measure_lean.py ingest-registry RESULTS`.
set -u
HERE=$(dirname "$(realpath "$0")")
JOBS=$(realpath "$1"); RES=$(realpath -m "$2"); LIMIT=${3:-1200}; RETRY=${4:-3600}; PAR=${5:-6}
export PATH=$HOME/.elan/bin:$PATH
mkdir -p "$RES"
done_() { [ -e "$RES/$1.done" ]; }
mark() { touch "$RES/$1.done"; echo "$(date -Is) $1 done"; }

if ! done_ host; then
  mt=$(curl -s -H 'Metadata-Flavor: Google' \
       http://metadata.google.internal/computeMetadata/v1/instance/machine-type | sed 's#.*/##')
  python3 - "$RES/host.json" "$mt" "$(lake env lean --version)" <<'EOF'
import json, os, sys
mem_kb = int(next(l for l in open("/proc/meminfo") if l.startswith("MemTotal")).split()[1])
nominal = {"e2-standard-8": 32}       # GB, as GCE sells the machine type; mem_total_gib is what the kernel sees
manifest = json.load(open("lake-manifest.json"))
json.dump({"name": os.uname().nodename, "machine": f"GCP {sys.argv[2]}", "cpus": os.cpu_count(),
           "ram_gb": nominal.get(sys.argv[2], round(mem_kb / 2**20)), "mem_total_gib": round(mem_kb / 2**20, 1),
           "lean_version": sys.argv[3].strip(),
           "mathlib_rev": next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")},
          open(sys.argv[1], "w"), indent=1)
EOF
  cat "$RES/host.json"; mark host
fi
if ! done_ build; then
  lake exe cache get && lake build PhysVerify && mark build || exit 1
fi
if ! done_ jobs; then
  "$HERE/lean_run_jobs.sh" "$JOBS" "$RES" "$LIMIT" "$PAR" && mark jobs
fi
if ! done_ retry; then
  mkdir -p "$JOBS/../jobs_retry"
  for ex in "$RES"/*.exit; do
    c=$(cat "$ex"); h=$(basename "$ex" .exit)
    if [ "$c" = 124 ] || [ "$c" = 137 ]; then cp "$JOBS/$h.lean" "$JOBS/../jobs_retry/"; fi
  done
  if ls "$JOBS/../jobs_retry/"*.lean >/dev/null 2>&1; then
    "$HERE/lean_run_jobs.sh" "$JOBS/../jobs_retry" "${RES}_retry" "$RETRY" 1 || exit 1
    cp "$RES/host.json" "${RES}_retry/"
  fi
  mark retry
fi
if ! done_ registry; then
  cp "$JOBS/../registry.lean" "$RES/registry.lean"
  /usr/bin/time -f "%e %M" -o "$RES/registry.time" lake env lean "$RES/registry.lean" > "$RES/registry.log" 2>&1
  echo $? > "$RES/registry.exit"
  mark registry
fi
echo MEASURE_DONE
