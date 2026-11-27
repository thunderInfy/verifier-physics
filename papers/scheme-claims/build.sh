#!/usr/bin/env bash
# Build main.pdf with tectonic; fail on undefined references or overfull boxes.
# The first build of a new package needs network (tectonic fetches it once, then caches it).
set -euo pipefail
cd "$(dirname "$0")"
TECTONIC=${TECTONIC:-$(command -v tectonic || echo "$HOME/.local/bin/tectonic")}
"$TECTONIC" -X compile main.tex --keep-logs
if grep -E 'undefined|Overfull' main.log; then
  echo "build.sh: undefined references or overfull boxes (above)" >&2
  exit 1
fi
