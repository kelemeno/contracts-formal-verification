import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4006823798342809328
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_8218475617004033221
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7020639558537270069
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_294889826768454570
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_2693611967757691411_gen


namespace L2InteropCommitmentTree.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def ACond_for_2693611967757691411 (s₀ : State) : Literal := 1
/-- The state the first break guard sees: the level count loaded and compared. -/
def levelGuardState (s₀ : State) : State :=
  let gs := s₀⟦"split_expr_5" ↦ Clear.EVMState.sload s₀.evm 0⟧
  gs⟦"split_expr_6" ↦ (decide (gs["var_i"]!! < (gs["split_expr_5"]!!))).toUInt256⟧

/-- Loop post: `var_i := add(var_i, 1)`. -/
def APost_for_2693611967757691411 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"var_i" ↦ ((Ok evm store)["var_i"]!! + 1)⟧

/-- **Loop postcondition.**  This loop is `for { } 1 { … }` — the condition is the
literal 1, so it NEVER exits through the condition and `AZero` is vacuous.  Everything
the loop guarantees on exit therefore comes from its two `break`s, and that is what
this says: on exit either the level-bound flag came out false (`split_expr_6 = 0`,
i.e. the level index reached the stored count — see `levelGuardState_flag_iff` for
that reading) or the two node counts had met.

Stating it via the compiled flag rather than the underlying comparison is what keeps
the closure lemmas mechanical; the meaning lemma below recovers the comparison. -/
def AFor_for_2693611967757691411 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₉ = Ok evm store →
    ((Ok evm store)["split_expr_6"]!! = 0 ∨
      (Ok evm store)["var_oldMaxNodeNumber"]!! = (Ok evm store)["var_maxNodeNumber"]!!)

/-- Loop body: check the two break conditions, copy level `i`'s node, halve both counts. -/
def ABody_for_2693611967757691411 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec A_if_4006823798342809328 (levelGuardState s₀) s₁ ∧
    ∃ s₂, Spec A_if_8218475617004033221 s₁ s₂ ∧
      ∃ s₃, Spec A_block_7020639558537270069 s₂ s₃ ∧
        ∃ s₄, Spec A_block_294889826768454570 s₃ s₄ ∧
          s₉ = s₄

/-- **What the flag means**: it is zero exactly when the level index has reached the
stored level count, which is the loop's "no more levels" exit. -/
lemma levelGuardState_flag_iff {s : State} (hok : isOk s) :
    (levelGuardState s)["split_expr_6"]!! = 0 ↔
      ¬ (s["var_i"]!! < Clear.EVMState.sload s.evm 0) := by
  unfold levelGuardState
  rw [lookup_insert' (by simpa [isOk_insert] using hok),
    lookup_insert_of_ne (by decide), lookup_insert' hok]
  by_cases hlt : s["var_i"]!! < Clear.EVMState.sload s.evm 0
  · simp [hlt]
  · simp [hlt]

lemma for_2693611967757691411_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_2693611967757691411_post_concrete_of_code s₀ s₉ →
  Spec APost_for_2693611967757691411 s₀ s₉ := by
  unfold for_2693611967757691411_post_concrete_of_code APost_for_2693611967757691411
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma for_2693611967757691411_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_2693611967757691411_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_2693611967757691411 s₀ s₉ := by
  unfold for_2693611967757691411_body_concrete_of_code ABody_for_2693611967757691411 levelGuardState
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq.symm⟩

/-- Vacuous: the loop condition is the literal `1`, so it is never `0`. -/
lemma AZero_for_2693611967757691411 : ∀ s₀, isOk s₀ → ACond_for_2693611967757691411 (👌 s₀) = 0 → AFor_for_2693611967757691411 s₀ s₀ := by
  intro s₀ _hok hcond
  unfold ACond_for_2693611967757691411 at hcond
  exact absurd hcond (by decide)

lemma AOk_for_2693611967757691411 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_2693611967757691411 s₀ = 0 → ABody_for_2693611967757691411 s₀ s₂ → APost_for_2693611967757691411 s₂ s₄ → Spec AFor_for_2693611967757691411 s₄ s₅ → AFor_for_2693611967757691411 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 h2 h5 _hcond _hbody hpost hspec
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have h4 : s₄ = (Ok e2 st2)⟦"var_i" ↦ ((Ok e2 st2)["var_i"]!! + 1)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    exact Spec_ok_unfold (P := AFor_for_2693611967757691411) (s := s₄) (s' := s₅) hok4 h5 hspec
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])

lemma AContinue_for_2693611967757691411 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_2693611967757691411 s₀ = 0 → ABody_for_2693611967757691411 s₀ s₂ → Spec APost_for_2693611967757691411 (🧟s₂) s₄ → Spec AFor_for_2693611967757691411 s₄ s₅ → AFor_for_2693611967757691411 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 _h2 _hcond _hbody _hpost hspec
  intro evm store hs
  have h5 : ¬ ❓ s₅ := by rw [hs]; simp [State.isOutOfFuel]
  rcases s₄ with ⟨e4, st4⟩ | _ | _
  · exact Spec_ok_unfold (P := AFor_for_2693611967757691411) (by simp [isOk]) h5 hspec evm store hs
  · exact absurd (hspec) (by rw [hs] at *; simp [Spec, State.isOutOfFuel])
  · exact absurd (hspec) (by rw [hs] at *; simp [Spec, State.isJump])

/-- **The main exit.**  A `break` can only come from one of the two guards, and every
step after it merely carries the checkpoint along — so the state the loop revives is
the one live AT THE BREAK, and the guard's branch condition is exactly the disjunct
`AFor` needs.  If neither guard breaks the body ends `Ok`, contradicting `isBreak`. -/
lemma ABreak_for_2693611967757691411 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_2693611967757691411 s₀ = 0 → ABody_for_2693611967757691411 s₀ s₂ → AFor_for_2693611967757691411 s₀ (🧟s₂) := by
  intro s₀ sb h0 hb _hcond hbody
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := hbody
  rw [heq] at hb ⊢
  have h4nf : ¬ ❓ s₄ := by
    rcases s₄ with ⟨e, st⟩ | _ | c
    · simp [State.isOutOfFuel]
    · simp [State.isBreak] at hb
    · simp [State.isOutOfFuel]
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (levelGuardState s₀) := by
    unfold levelGuardState; simp only [isOk_insert]; exact h0
  have hg1 := Spec_ok_unfold hgc h1nf h₁
  by_cases hf1 : (levelGuardState s₀)["split_expr_6"]!! = 0
  · have e1 : s₁ = 💔(levelGuardState s₀) := hg1.1 hf1
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj2 : isJump (.Break be bst) s₂ := Clear.isJump_of_Spec_of_isJump h₂ hj1
    have hj3 : isJump (.Break be bst) s₃ := Clear.isJump_of_Spec_of_isJump h₃ hj2
    rw [Clear.reviveJump_eq_of_Spec_of_isJump h₄ hj3,
      Clear.reviveJump_eq_of_Spec_of_isJump h₃ hj2,
      Clear.reviveJump_eq_of_Spec_of_isJump h₂ hj1, e1, Clear.reviveJump_setBreak hgc]
    intro evm store hs
    left
    rw [← hs]
    exact hf1
  · have e1 : s₁ = levelGuardState s₀ := hg1.2 hf1
    have hs1ok : isOk s₁ := by rw [e1]; exact hgc
    have hg2 := Spec_ok_unfold hs1ok h2nf h₂
    by_cases hf2 : s₁["var_oldMaxNodeNumber"]!! = s₁["var_maxNodeNumber"]!!
    · have e2 : s₂ = 💔s₁ := hg2.1 hf2
      have hb2 : isBreak s₂ := by rw [e2]; exact Clear.isBreak_setBreak hs1ok
      obtain ⟨be, bst, hj2⟩ := Clear.isJump_Break_of_isBreak hb2
      have hj3 : isJump (.Break be bst) s₃ := Clear.isJump_of_Spec_of_isJump h₃ hj2
      rw [Clear.reviveJump_eq_of_Spec_of_isJump h₄ hj3,
        Clear.reviveJump_eq_of_Spec_of_isJump h₃ hj2, e2, Clear.reviveJump_setBreak hs1ok]
      intro evm store hs
      right
      rw [← hs]
      exact hf2
    · exfalso
      have e2 : s₂ = s₁ := hg2.2 hf2
      have hs2ok : isOk s₂ := by rw [e2]; exact hs1ok
      have hs3ok : isOk s₃ := block_7020639558537270069_isOk hs2ok h3nf (Spec_ok_unfold hs2ok h3nf h₃)
      have hs4ok : isOk s₄ := block_294889826768454570_isOk hs3ok h4nf (Spec_ok_unfold hs3ok h4nf h₄)
      exact not_isOk_of_isBreak hb hs4ok

lemma ALeave_for_2693611967757691411 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_2693611967757691411 s₀ = 0 → ABody_for_2693611967757691411 s₀ s₂ → AFor_for_2693611967757691411 s₀ s₂ := by
  intro s₀ s₂ _h0 h2 _hcond _hbody
  intro evm store hs
  rcases s₂ with _ | _ | c
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd hs (by simp)

end

end L2InteropCommitmentTree.Common
