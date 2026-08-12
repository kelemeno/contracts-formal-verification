#!/usr/bin/env bash
# Emit the seven MECHANICAL obligations of a Yul for-loop spec.
#
# The generator leaves 12 sorries per loop. For a COUNTED loop with no break /
# continue / leave in its body, seven of the eight obligations depend only on the
# loop's shape, not on what the body does:
#
#   ACond, APost, AFor, AZero, AOk, AContinue, ALeave
#
# and only ABody (plus ABreak, which reads off ABody) needs the body's closed form.
# Derived on for_4476381376322263891 (callStatus write) and re-used unchanged on
# for_7012656997412934425 (calldata copy), where it took 12 sorries to 3 in one pass.
#
# THE KEY CHOICE, without which none of this is mechanical: AFor is a property of
# s₉ ALONE ("on normal exit the cursor has reached the bound"). That is what lets
# the closure lemmas thread it through the recursion unchanged, and it is sound
# whenever the bound variable is untouched by body and post.
#
# Usage:
#   scripts/loop-spec-skeleton.sh <loop_id> <cursor_var> <bound_var> <increment>
# e.g.
#   scripts/loop-spec-skeleton.sh for_7012656997412934425 src srcEnd 32
#
# Writes the skeleton to stdout, INCLUDING an ABody placeholder in the correct
# position (above the lemmas -- AOk/AContinue/ALeave reference it, and defining it
# after them fails with 'unknown identifier'). Build, then mirror ABody's true form
# from the type-mismatch message, and write ABreak from it.
set -euo pipefail

if [ $# -ne 4 ]; then
  echo "usage: $(basename "$0") <loop_id> <cursor_var> <bound_var> <increment>" >&2
  echo "example: $(basename "$0") for_7012656997412934425 src srcEnd 32" >&2
  exit 1
fi

N="$1"; CUR="$2"; BOUND="$3"; INC="$4"

cat <<EOF
/-- Loop condition: \`lt($CUR, $BOUND)\`. -/
def ACond_$N (s₀ : State) : Literal :=
  fromBool (s₀["$CUR"]!! < s₀["$BOUND"]!!)

/-- Loop post: \`$CUR := add($CUR, $INC)\`. -/
def APost_$N (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"$CUR" ↦ ((Ok evm store)["$CUR"]!! + $INC)⟧

/-- Loop postcondition: on normal exit the cursor has REACHED the bound, so the body
ran for every step. A property of \`s₉\` alone -- that is what lets the closure lemmas
thread it through unchanged, and it is sound because \`$BOUND\` is untouched by body
and post. -/
def AFor_$N (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₉ = Ok evm store → ¬ ((Ok evm store)["$CUR"]!! < (Ok evm store)["$BOUND"]!!)

/-- Loop body — PLACEHOLDER. Build, then mirror the true form from the type-mismatch
message. It must be defined HERE, above the lemmas: AOk/AContinue/ALeave reference it. -/
def ABody_$N (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store → s₉ = Ok evm store

lemma ${N}_cond_abs_of_code {s₀ fuel} : eval fuel ${N}_cond (s₀) = (s₀, ACond_$N (s₀)) := by
  unfold eval ACond_$N
  simp [${N}_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma ${N}_concrete_of_post_abs {s₀ s₉ : State} :
  Spec ${N}_post_concrete_of_code s₀ s₉ →
  Spec APost_$N s₀ s₉ := by
  unfold ${N}_post_concrete_of_code APost_$N
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma AZero_$N : ∀ s₀, isOk s₀ → ACond_$N (👌 s₀) = 0 → AFor_$N s₀ s₀ := by
  intro s₀ hok hcond
  unfold AFor_$N ACond_$N at *
  intro evm store hs
  subst hs
  intro hlt
  -- the guard evaluated to 0, so the comparison it decided was false
  simp only [State.mkOk] at hcond
  simp [fromBool, Bool.toUInt256, hlt] at hcond

lemma AOk_$N : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_$N s₀ = 0 → ABody_$N s₀ s₂ → APost_$N s₂ s₄ → Spec AFor_$N s₄ s₅ → AFor_$N s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 h2 h5 _hcond _hbody hpost hspec
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have h4 : s₄ = (Ok e2 st2)⟦"$CUR" ↦ ((Ok e2 st2)["$CUR"]!! + $INC)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    -- name the implicits: \`AFor\` ignores its first argument, but unification does not know that
    exact Spec_ok_unfold (P := AFor_$N) (s := s₄) (s' := s₅) hok4 h5 hspec
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])

lemma AContinue_$N : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_$N s₀ = 0 → ABody_$N s₀ s₂ → Spec APost_$N (🧟s₂) s₄ → Spec AFor_$N s₄ s₅ → AFor_$N s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 _h2 _hcond _hbody _hpost hspec
  intro evm store hs
  -- no reasoning about the continue state is needed: case on s₄ and read Spec off its definition
  have h5 : ¬ ❓ s₅ := by rw [hs]; simp [State.isOutOfFuel]
  rcases s₄ with ⟨e4, st4⟩ | _ | c4
  · exact Spec_ok_unfold (P := AFor_$N) (s := Ok e4 st4) (s' := s₅) (by simp [isOk]) h5 hspec evm store hs
  · exact absurd (by simpa [Spec] using hspec) h5
  · have hj : s₅.isJump c4 := by simpa [Spec] using hspec
    rw [hs] at hj
    exact absurd hj (by simp [State.isJump])

lemma ALeave_$N : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_$N s₀ = 0 → ABody_$N s₀ s₂ → AFor_$N s₀ s₂ := by
  intro s₀ s₂ _h0 h2 _hcond _hbody
  -- a leave state is a Checkpoint, so the postcondition's hypothesis is unsatisfiable
  intro evm store hs
  rcases s₂ with _ | _ | c
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd hs (by simp)

-- ABody: write a placeholder (\`s₉ = Ok evm store\`), build, and mirror the closed form
-- from the type-mismatch message.
--
-- ABreak: with an INLINE body, its closed form exhibits the output as an insert/setEvm
-- chain on an Ok, so the Checkpoint case dies at once:
--     rcases s₀ with ⟨e0, st0⟩ | _ | _
--     · have hA := hbody e0 st0 rfl
--       rcases s₂ with _ | _ | c
--       · exact absurd h2 (by simp [State.isBreak])
--       · simp [State.insert, State.setEvm] at hA
--       · simp [State.insert, State.setEvm] at hA
--     · exact absurd h0 (by simp [isOk])
--     · exact absurd h0 (by simp [isOk])
-- With a BLOCK-DECOMPOSED body you must walk the Spec chain instead: an out-of-fuel
-- intermediate cannot be ruled out directly (Spec's Ok branch is only ¬❓s₁ → A s₀ s₁),
-- so case on each intermediate as Ok / OutOfFuel / Checkpoint -- OutOfFuel propagates to
-- an out-of-fuel output, Checkpoint propagates UP and dies at the first block. See
-- for_4476381376322263891 for the worked instance.
--
-- In BOTH cases the closer is \`simp [..., State.insert, State.setEvm]\`: without those
-- two unfolds simp cannot see the constructor clash and leaves the goal open.
EOF
