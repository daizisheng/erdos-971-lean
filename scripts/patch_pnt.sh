#!/usr/bin/env bash
# Copy the vendored PrimeNumberTheoremAnd files (see vendor/PrimeNumberTheoremAnd-f8f58c7/README.md)
# over the dependency checkout. Run once after `lake update`, before `lake build`.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SRC="$ROOT/vendor/PrimeNumberTheoremAnd-f8f58c7"
DST="$ROOT/.lake/packages/PrimeNumberTheoremAnd"
[ -d "$DST" ] || { echo "run 'lake update' first" >&2; exit 1; }
cd "$SRC"
find PrimeNumberTheoremAnd -name '*.lean' | while read -r f; do
  mkdir -p "$DST/$(dirname "$f")"
  cp "$f" "$DST/$f"
done
echo "patched $DST from $SRC"
