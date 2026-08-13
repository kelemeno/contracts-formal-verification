#!/usr/bin/env bash
# Port a closed spec from one contract to another, but ONLY if the Yul is identical.
#
# solc emits the same helper into every contract that needs it -- panic_error_0x11,
# checked_sub_uint256, fun_efficientHash, the storage-array accessors -- so closing one
# and porting is far cheaper than reproving.  Done by hand six times in one session
# before this script existed.
#
# The check that makes it safe: diff the two generated function bodies with the name
# normalised away, and refuse to port if they differ.  Two traps this catches:
#
#   * solc emits MULTIPLE copies of a helper with numeric suffixes (eight of the
#     storage-array accessor in L2InteropCommitmentTree alone), and they are NOT all
#     the same -- some are specialised with the slot inlined and take fewer arguments.
#     Porting onto the wrong copy would produce a spec that builds and says the wrong
#     thing about a different function.
#   * a helper can drift between contracts if they were compiled from different
#     sources.
#
# After copying, the target is BUILT.  A port that does not build is reverted, so a
# failed port leaves the tree exactly as it was.
#
# Usage: scripts/port-spec.sh <spec_name> <from_contract> <to_contract>
#   e.g. scripts/port-spec.sh checked_sub_uint256 AtomicFlowManager L2InteropCommitmentTree
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

[ $# -eq 3 ] || { echo "usage: $0 <spec_name> <from_contract> <to_contract>"; exit 2; }
NAME="$1"; FROM="$2"; TO="$3"

src=$(find "specs/$FROM" -name "${NAME}_user.lean" 2>/dev/null | head -1)
dst=$(find "specs/$TO"   -name "${NAME}_user.lean" 2>/dev/null | head -1)
gsrc=$(find "generated/$FROM" -name "${NAME}_gen.lean" 2>/dev/null | head -1)
gdst=$(find "generated/$TO"   -name "${NAME}_gen.lean" 2>/dev/null | head -1)
for f in "$src" "$dst" "$gsrc" "$gdst"; do
  [ -n "$f" ] || { echo "FAIL  $NAME: missing spec or generated file in $FROM/$TO"; exit 1; }
done

# The Yul body, with the definition name stripped so only the CODE is compared.
body() { sed -n "/^def ${NAME} /,/^>/p" "$1" | sed "s/${NAME}//g"; }
if ! diff <(body "$gsrc") <(body "$gdst") > /tmp/port_diff_$$.txt 2>&1; then
  echo "FAIL  $NAME: Yul differs between $FROM and $TO -- NOT porting"
  head -12 /tmp/port_diff_$$.txt
  rm -f /tmp/port_diff_$$.txt
  exit 1
fi
rm -f /tmp/port_diff_$$.txt

cp "$dst" "/tmp/port_backup_$$.lean"
python3 - "$src" "$dst" "$NAME" "$FROM" "$TO" <<'PY'
import sys
src, dst, name, frm, to = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5]
a, b = open(src).read(), open(dst).read()
i = a.index('def A_' + name)
j = a.index('\nend\n\nend ')
k = a.rfind('/--', 0, i)
if k != -1 and a[k:i].count('-/') == 1:
    i = k                      # carry the docstring
sec = a[i:j]
# A ported spec refers to its sibling guards through the SOURCE contract's Common
# namespace; those siblings exist under the target's own Common namespace instead.
# Without this the port builds nowhere and reverts, which is safe but useless.
sec = sec.replace(frm + '.Common.', to + '.Common.')
c = b.index('def A_' + name)
d = b.index('\nend\n\nend ')
k2 = b.rfind('/--', 0, c)
if k2 != -1 and b[k2:c].count('-/') == 1:
    c = k2
# keep the target's own imports; StateOk may be needed by the ported proofs
if 'import specs.StateOk' not in b and 'StateOk' in sec:
    b = b.replace('import Clear.ReasoningPrinciple',
                  'import Clear.ReasoningPrinciple\nimport specs.StateOk', 1)
    c = b.index('def A_' + name)
    d = b.index('\nend\n\nend ')
    k2 = b.rfind('/--', 0, c)
    if k2 != -1 and b[k2:c].count('-/') == 1:
        c = k2
open(dst, 'w').write(b[:c] + sec + b[d:])
PY

mod=$(echo "$dst" | sed 's|^specs/|specs.|; s|/|.|g; s|\.lean$||')
if ~/.elan/bin/lake build --old "$mod" > /tmp/port_build_$$.log 2>&1; then
  echo "ok    $NAME  $FROM -> $TO"
  rm -f "/tmp/port_backup_$$.lean" /tmp/port_build_$$.log
else
  echo "FAIL  $NAME: ported but does not build in $TO -- reverting"
  grep -E "^error" -A4 /tmp/port_build_$$.log | grep -v "linter\|note:" | head -8
  cp "/tmp/port_backup_$$.lean" "$dst"
  rm -f "/tmp/port_backup_$$.lean" /tmp/port_build_$$.log
  exit 1
fi
