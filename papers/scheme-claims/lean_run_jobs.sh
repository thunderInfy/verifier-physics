#!/usr/bin/env bash
# Usage (on the Lean machine): lean_run_jobs.sh JOBS RESULTS LIMIT_S PARALLEL
#
# Runs `lake env lean` on every JOBS/<sha>.lean that has no RESULTS/<sha>.exit yet, PARALLEL at a time,
# each under its own wall-clock limit (coreutils `timeout`, which signals the whole process group: exit
# 124 is a timeout). For each file: <sha>.log (Lean's output), <sha>.time ("wall_s peak_rss_kb") and,
# written last, <sha>.exit. A crash or a shutdown leaves no .exit, so rerunning resumes where it stopped.
# Run from lean/ (the project with Mathlib built). measure_lean.py writes the jobs and reads the results.
set -u
JOBS=$(realpath "$1"); RESULTS=$(realpath -m "$2"); LIMIT=$3; PAR=$4
mkdir -p "$RESULTS"
echo "$LIMIT" > "$RESULTS/limit"
export PATH=$HOME/.elan/bin:$PATH RESULTS LIMIT
date +%s > "$RESULTS/run.start.$(date +%s)"
one() {
  f=$1; h=$(basename "$f" .lean)
  [ -e "$RESULTS/$h.exit" ] && return 0
  /usr/bin/time -f "%e %M" -o "$RESULTS/$h.time" timeout -k 30 "$LIMIT" lake env lean "$f" > "$RESULTS/$h.log" 2>&1
  echo $? > "$RESULTS/$h.exit.tmp" && mv "$RESULTS/$h.exit.tmp" "$RESULTS/$h.exit"
}
export -f one
ls "$JOBS"/*.lean | xargs -P "$PAR" -I{} bash -c 'one "$1"' _ {}
date +%s > "$RESULTS/run.end.$(date +%s)"
echo ALL_DONE
