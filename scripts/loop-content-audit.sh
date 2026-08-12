#!/usr/bin/env bash
# Classify every for-loop spec by whether it says anything.
#
# A loop spec can be `sorry`-free, axiom-clean, and green, while proving nothing:
# the generator's obligations are discharged by setting
#
#     def AFor_<id> (s₀ s₉ : State) : Prop := True
#     def APost_<id> := <id>_post_concrete_of_code.1     -- alias to the concrete spec
#     def ABody_<id> := <id>_body_concrete_of_code.1     -- ditto
#
# after which AZero/AOk/AContinue/ABreak/ALeave all close with `trivial`. That is the
# loop-level form of the tautological block specs this project already tracks, and it is
# why neither a sorry count nor a green build is a progress metric here.
#
# Categories:
#   REAL        AFor is a genuine postcondition, no sorries
#   TRUE-FOR    AFor := True  -- discharged, contentless
#   PARTIAL     some obligations proven, others still sorry
#   ALIAS       APost or ABody defined as the concrete spec (reported alongside)
#
# Usage: scripts/loop-content-audit.sh [--list]
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

LIST="${1:-}"
real=0; truefor=0; partial=0; alias_n=0; total=0
real_files=(); truefor_files=(); partial_files=()

while IFS= read -r f; do
  total=$((total + 1))
  if grep -qE '^def AFor_[0-9a-zA-Z_]+ .*:= True' "$f" 2>/dev/null; then
    truefor=$((truefor + 1)); truefor_files+=("$f")
  elif grep -q 'sorry' "$f" 2>/dev/null; then
    partial=$((partial + 1)); partial_files+=("$f")
  else
    real=$((real + 1)); real_files+=("$f")
  fi
  if grep -qE '^def A(Post|Body)_[0-9a-zA-Z_]+ .*:= .*_concrete_of_code' "$f" 2>/dev/null; then
    alias_n=$((alias_n + 1))
  fi
done < <(find specs -name "for_*_user.lean" | sort)

echo "for-loop specs: $total"
echo "  REAL      $real   genuine closed form, no sorries"
echo "  TRUE-FOR  $truefor   AFor := True -- green, axiom-clean, and contentless"
echo "  PARTIAL   $partial   some obligations proven, body transcription remaining"
echo "  (ALIAS    $alias_n   APost/ABody aliased to the concrete spec)"

if [ "$LIST" = "--list" ]; then
  echo; echo "REAL:";     printf '  %s\n' "${real_files[@]:-}"
  echo; echo "PARTIAL:";  printf '  %s\n' "${partial_files[@]:-}"
  echo; echo "TRUE-FOR:"; printf '  %s\n' "${truefor_files[@]:-}"
fi

echo
echo "To give a TRUE-FOR loop content, use scripts/loop-spec-skeleton.sh: it emits the"
echo "seven obligations that depend only on loop shape, leaving ABody (and ABreak) per loop."
