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

-- !! THE PROBE SHAPE IS NOT SOUND AS A TEST OF A SPEC. Writing \`A := (s₉ = s₀)\` and closing
-- with \`apply spec_eq; intro _hne hc; exact hc\` BUILDS against non-trivial concrete specs --
-- observed on switch_7706602271607130061, if_1209118431116190868 and if_6747681429752853338,
-- all of which have real content. Use the probe ONLY to read the type-mismatch message, never
-- as evidence that a spec is right. To see the emitted C reliably:
--     example (s₀ s₉ : State) (h : <name>_concrete_of_code.1 s₀ s₉) : True := by
--       unfold <name>_concrete_of_code at h; trace_state; trivial
-- and to check a FINISHED spec, append \`∧ False\` to it and confirm the build FAILS.
--
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
--
-- WHEN NOT TO CONVERT AT ALL. If the body composes through FUNCTION specs that are still
-- aliases (\`A_<fn> := <fn>_concrete_of_code.1\`), ABody transcribes fine but ABreak does
-- NOT close: nothing forces the intermediate states to be Ok, because the alias is
-- opaque. Converting anyway would leave the loop PARTIAL, and a converted-but-partial
-- loop introduces sorryAx into every dependent -- where the vacuous TRUE-FOR version was
-- clean. A contentless-but-clean loop beats a half-done one. Give the accessor functions
-- closed forms FIRST, then the loop follows. (Hit on
-- AtomicFlowManager for_6242390032430749259 / for_423567071893050842, whose bodies go
-- through calldata_array_index_access_* and memory_array_index_access_struct_*.)
--
-- ...AND CLOSING THE HELPERS IS NECESSARY BUT NOT SUFFICIENT. With all four helpers/guards
-- given closed forms, that loop's ABreak still does not close: each Spec in the chain adds
-- its own Ok / OutOfFuel / Checkpoint case, and a function spec whose conclusion is itself
-- an existential adds another level below that. Walking it inline does not terminate in
-- any readable way.
-- The right factoring is one REUSABLE lemma per helper, proved once:
--     lemma <fn>_never_checkpoint : Spec (A_<fn> args) s₀ s₉ → isOk s₀ → ¬ isBreak s₉
-- (or the stronger "output is Ok"). Then ABreak is three rewrites instead of a nested
-- case analysis. Prove those before attempting the loop again.
--
-- WORKED INSTANCE (AtomicFlowManager, 2026-08-12): closing panic_error_0x11/0x32, three
-- guards and two accessors -- each with a closed form AND an isOk/not_break lemma -- turned
-- for_6242390032430749259'"'"'s ABreak into four \`have\`s. The sibling loop then ported with two
-- search-and-replaces. The isOk lemmas chain: ¬ ❓ s₉ propagates BACKWARDS through the body
-- (isOutOfFuel_insert'"'"'/setStore'"'"'/reviveJump'"'"'/multifill'"'"'), so the caller supplies it once.
--
-- A BODY CONTAINING keccak256: SOLVED, and not the way you would guess. Its ABody carries an
-- Option match (the collision fallback) whose pretty-printed form does NOT disambiguate how
-- \`multifill\` associates with the match result, so transcribing from the error message fails.
-- Hand-writing the match fails too, and so does the accOut/keccakOut helper -- both differ
-- structurally from what the generator emits.
-- What works is mirroring the generated proof's own primitive. The gen file does
-- \`rw [EVMKeccak256']\`, and that lemma says the call IS a pair, so write:
--
--     multifill ["<var>"] (primCall b .Keccak256 [0, 64]).2 (primCall b .Keccak256 [0, 64]).1 = s₉
--
-- with \`b\` the state after the two scratch mstores, and close with a bare \`exact hc\` -- do NOT
-- \`rw [EVMKeccak256']\` yourself, the unfolded goal has the match already expanded. Verified on
-- for_5976315420052011104. GENERAL RULE: when the error message is ambiguous, mirror the
-- PRIMITIVE the generated proof rewrites with, not the term the pretty-printer shows.
--
-- ...and note the knock-on for that loop'"'"'s ABreak: the frame lemmas
-- (isOutOfFuel_setEvm'"'"'/multifill'"'"') do NOT fire through \`(primCall b .Keccak256 [0,64]).1\`,
-- because that projection is a match, not a syntactic setEvm. Case on
-- \`b.evm.keccak256 0 64\` FIRST (some/none), after which each branch is a setEvm and the
-- frame lemmas apply. Everything else that loop needs is closed: both its guards carry
-- isOk/not_break, and its ABody goes through.
--
-- Three ABreak assemblies attempted for it; none landed. What did NOT work: casing on keccak
-- inline before the frame rewrites (h2 keeps the un-cased form, so the sides stop matching);
-- and a \`private lemma\` pair for the projection (right idea, but the not-out-of-fuel
-- direction needs the case on the SAME scrutinee the goal mentions, which the helper hides).
-- The shape that should work is that pair stated with X UNIVERSALLY QUANTIFIED --
--     keccak_proj_isOk : isOk X -> isOk (primCall X .Keccak256 [0,64]).1
--     keccak_proj_nf   : out-of-fuel (primCall X .Keccak256 [0,64]).1 -> out-of-fuel X
-- proved by \`rcases hk : X.evm.keccak256 0 64 <;> simp [EVMKeccak256\', hk, ...]\`, then used
-- with NO further casing in ABreak. Do the not-out-of-fuel direction first and in isolation:
-- chaining it through the break/out-of-fuel exclusion is what failed each time.
--
-- BODIES THAT CAN REVERT (an \`if ... { revert(0, 0) }\` in the body) do NOT break any of
-- the seven obligations above -- they key on loop shape, not body content. Only ABody and
-- ABreak change:
--   * ABody goes through the if-block's own proven spec (A_if_<id>) as an existential,
--     rather than being a straight-line insert/setEvm chain.
--   * ABreak still works, because a REVERT IS NOT A BREAK: \`evm_revert\` sets a flag on an
--     Ok state, so the guard output is Ok-constructed on both branches. Do NOT case-split
--     on the guard value -- that forces you to write out the whole zeta-expanded scratch
--     expression. Unfold the guard inside the hypothesis instead:
--         simp [Spec, A_if_<id>, State.insert, State.setEvm] at hif
--     which refutes both branches at once. See for_7496197131413067314.
EOF
