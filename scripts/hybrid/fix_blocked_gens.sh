#!/usr/bin/env bash
# Iteratively fix all blocked gen files for a contract by replacing their broken
# concrete_of_code proofs with the generic operational-semantics proof.
# Build all user targets -> collect failing _gen files -> patch each (block vs fn shape) -> repeat.
# Usage: fix_blocked_gens.sh <Contract>
set -uo pipefail
cd "$(dirname "$0")/../.."
export PATH="$HOME/.elan/bin:$PATH"
C="${1:?contract}"
ROUND=0
while [ "$ROUND" -lt 8 ]; do
  ROUND=$((ROUND+1))
  echo "=== round $ROUND: build all $C user targets ==="
  targets=()
  for f in specs/$C/$C/*_user.lean specs/$C/$C/Common/*_user.lean; do
    [ -f "$f" ] || continue
    rel="${f#specs/$C/$C/}"; rel="${rel%_user.lean}"
    case "$f" in
      */Common/*) targets+=("specs.$C.$C.Common.$(basename "$f" .lean)") ;;
      *)          targets+=("specs.$C.$C.$(basename "$f" .lean)") ;;
    esac
  done
  log="/tmp/fixgen_${C}_${ROUND}.log"
  lake build --old "${targets[@]}" > "$log" 2>&1
  # failing gen files (own errors), unique
  mapfile -t fails < <(grep -E "error:" "$log" | grep -oE "generated/$C/$C/[A-Za-z0-9_/]+_gen\.lean" | sort -u)
  echo "failing gens this round: ${#fails[@]}"
  if [ "${#fails[@]}" -eq 0 ]; then echo "ALL CLEAN"; break; fi
  changed=0
  for g in "${fails[@]}"; do
    if grep -q "execCall" <(sed -n "/_concrete_of_code/,/} := by/p" "$g"); then
      python3 scripts/hybrid/generic_concrete_fn.py "$g" && changed=1
    else
      python3 scripts/hybrid/generic_concrete.py "$g" && changed=1
    fi
  done
  echo "patched this round (changed=$changed)"
  [ "$changed" -eq 0 ] && { echo "no progress, stopping"; break; }
done
