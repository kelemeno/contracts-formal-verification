#!/usr/bin/env bash
# Identify the Solidity custom error behind a 4-byte revert selector.
#
# The compiled Yul reverts with a bare selector:
#
#     let split_expr_2 := shl(225, 2012753307)
#     mstore(0, split_expr_2)
#     revert(0, 4)
#
# which tells you nothing about WHICH check failed.  This resolves it against every
# `error` declaration in era-contracts, so a guard spec can name the error it
# enforces instead of quoting a magic number.  That naming is what connects a
# concrete guard to an abstract result -- if_6050018508198951540 turned out to be
# `ManagerBundleHashesNotSorted()`, i.e. the deployed end of FlowCanonical.lean.
#
# Note the shift is not always 224: solc emits `shl(225, sel >> 1)` when it can,
# so read the selector back with (v << bits) >> 224 rather than assuming.
#
# Usage:
#   scripts/error-selector.sh 0xeff05b36        # from a selector
#   scripts/error-selector.sh --shl 225 2012753307   # straight from the Yul
#
# Requires `cast` (foundry).  CONTRACTS_DIR overrides the era-contracts root.
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CONTRACTS_DIR="${CONTRACTS_DIR:-era-contracts}"

command -v cast >/dev/null || { echo "error: cast (foundry) not on PATH"; exit 2; }

if [ "${1:-}" = "--shl" ]; then
  [ $# -eq 3 ] || { echo "usage: $0 --shl <bits> <value>"; exit 2; }
  SEL=$(python3 -c "print(hex((int($3) << int($2)) >> 224))")
  echo "shl($2, $3) -> selector $SEL"
else
  SEL="${1:-}"
  [ -n "$SEL" ] || { echo "usage: $0 <0xselector> | --shl <bits> <value>"; exit 2; }
fi

SIGS=$(python3 - "$CONTRACTS_DIR" <<'PY'
import re, os, sys
root = sys.argv[1]
sigs = set()
pat = re.compile(r'\berror\s+([A-Za-z_]\w*)\s*\(([^)]*)\)\s*;', re.S)
for dp, _, fns in os.walk(root):
    for fn in fns:
        if not fn.endswith('.sol'):
            continue
        try:
            t = open(os.path.join(dp, fn), errors='ignore').read()
        except OSError:
            continue
        for m in pat.finditer(t):
            name, params = m.group(1), m.group(2)
            types = []
            for p in (x.strip() for x in params.split(',')):
                if not p:
                    continue
                ty = p.split()[0]
                # `uint`/`int` are aliases in a signature; everything else is literal
                if ty == 'uint':
                    ty = 'uint256'
                elif ty == 'int':
                    ty = 'int256'
                types.append(ty)
            sigs.add(f"{name}({','.join(types)})")
            # A selector is computed over ABI types, not declared ones: an ENUM parameter
            # encodes as uint8 and a CONTRACT/interface type as address.  Emitting the
            # declared name (`LegState`) yields a selector matching nothing, which is how a
            # real error looked undeclared until this was added.
            elementary = re.compile(r'^(u?int\d*|bytes\d*|bytes|string|address|bool)(\[\d*\])?$')
            if any(not elementary.match(t) for t in types):
                for repl in ('uint8', 'address'):
                    sigs.add(f"{name}({','.join(t if elementary.match(t) else repl for t in types)})")
print('\n'.join(sorted(sigs)))
PY
)

total=$(printf '%s\n' "$SIGS" | grep -c . )
echo "checking $total error declarations under $CONTRACTS_DIR"

found=0
while IFS= read -r sig; do
  [ -n "$sig" ] || continue
  s=$(cast sig "$sig" 2>/dev/null)
  if [ "$s" = "$SEL" ]; then
    echo "MATCH  $sig  ->  $s"
    found=$((found + 1))
  fi
done <<< "$SIGS"

if [ "$found" -eq 0 ]; then
  # A miss is informative: the error may live in a dependency, or the selector may
  # not be an error at all (solc uses the same shape for some function selectors).
  echo "no match -- selector is not a custom error declared under $CONTRACTS_DIR"
  echo "  (Solidity BUILT-INS are not declared with \`error\` and will never match:"
  echo "   Panic(uint256) = 0x4e487b71, Error(string) = 0x08c379a0.  A Panic payload"
  echo "   carries a code in the next word -- 0x21/33 is invalid-enum, 0x11/17 is"
  echo "   arithmetic overflow, 0x32/50 is array-out-of-bounds.)"
  exit 1
fi
