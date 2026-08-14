#!/usr/bin/env bash
# vacuity-check.sh — flag separation hypotheses that CANNOT be discharged.
#
# The failure mode this catches (found 2026-08-14 in two loop frames and their
# wrapper, all three green and axiom-clean at the time):
#
#     (hsep : ∀ j : UInt256, q ≠ base + j) → …
#
# Over a full word that hypothesis is UNSATISFIABLE — instantiate at j = q - base
# and it yields q ≠ q — so the lemma is provable and useless.  Nothing else in the
# checker set notices: it is not a stub, not an alias, and its postcondition is not
# `True`.  The fix is to bound the quantifier by the trip count:
#
#     ∃ n : ℕ, ∀ q, (∀ j : ℕ, j < n → q ≠ base + (j : UInt256)) → …
#
# A quantifier over ℕ is flagged too when it carries no bound: casting ℕ into
# UInt256 is onto, so `∀ j : ℕ, q ≠ base + j` is refutable in exactly the same way.
#
# Usage: scripts/vacuity-check.sh [path…]   (defaults to specs/)

set -uo pipefail
cd "$(dirname "$0")/.."

targets=("$@")
if [ ${#targets[@]} -eq 0 ]; then targets=(specs); fi

found=0
scanned=0

while IFS= read -r f; do
  scanned=$((scanned + 1))
  # Join each declaration onto one line so a hypothesis split across lines is seen
  # whole, then look for a full-word quantifier whose variable appears only as an
  # additive offset inside a `≠`, with no `<` bound on that same variable.
  python3 - "$f" <<'PY'
import re, sys
path = sys.argv[1]
src = open(path, encoding='utf-8').read()

# strip comments so prose examples do not match
src = re.sub(r'/-.*?-/', ' ', src, flags=re.S)
src = re.sub(r'--[^\n]*', ' ', src)

# each ∀ over a word-sized or ℕ variable, with the text that follows it
for m in re.finditer(r'∀\s+([A-Za-z][A-Za-z0-9_\']*)\s*:\s*(UInt256|ℕ)\s*,', src):
    var, ty = m.group(1), m.group(2)
    tail = src[m.end():m.end() + 400]
    # stop at the end of this binder's body (next ∀ or a closing paren run)
    body = re.split(r'∀\s+[A-Za-z]', tail)[0]
    if '≠' not in body:
        continue
    # the variable used as an additive offset: "+ j" or "+ (j : UInt256)"
    offset = re.search(r'\+\s*\(?\s*' + re.escape(var) + r'\b', body)
    if not offset:
        continue
    # a bound on the SAME variable makes it satisfiable -- including one stated on its
    # `.val`, which is how `KeccakSlotSep.Separated` writes it (an earlier version of this
    # regex missed that and reported it as the checker's own false alarm)
    bounded = re.search(re.escape(var) + r'(\.val)?\s*<', body)
    if bounded:
        continue
    line = src[:m.start()].count('\n') + 1
    print(f"VACUOUS?  {path}:{line}  ∀ {var} : {ty} used only as an unbounded offset in a ≠")
PY
done < <(find "${targets[@]}" -name '*.lean' -print) > /tmp/vacuity-check.out 2>/dev/null

cat /tmp/vacuity-check.out
# `grep -c` already prints 0 and exits 1 when there is no match, so a `|| echo 0`
# fallback appends a SECOND line and the later [ ] test dies on "0\n0"
found=$(grep -c "VACUOUS?" /tmp/vacuity-check.out 2>/dev/null)
found=${found:-0}

echo
if [ "$found" -eq 0 ]; then
  echo "no unbounded separation hypotheses found"
else
  echo "$found suspect hypothes(es) — check each by trying to derive False from it"
fi
