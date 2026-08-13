import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2425414531525476249
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mod_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_8961670722464898128
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_5022472617119597648
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_2896862189596047701
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_2268004712116198193_gen


namespace L2InteropCommitmentTree.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def ACond_for_2268004712116198193 (s₀ : State) : Literal := 1
/-- The state the break guard sees: the level count loaded and compared. -/
def rootGuardState (s₀ : State) : State :=
  let gs := s₀⟦"split_expr_3" ↦ Clear.EVMState.sload s₀.evm 0⟧
  gs⟦"split_expr_4" ↦ (decide (gs["var_i"]!! < (gs["split_expr_3"]!!))).toUInt256⟧

/-- Loop post: `var_i := add(var_i, 1)`. -/
def APost_for_2268004712116198193 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"var_i" ↦ ((Ok evm store)["var_i"]!! + 1)⟧

/-- **Loop postcondition.**  `for { } 1 { … }` with ONE break, so on exit the level
bound must have failed: the flag `split_expr_4` is zero, i.e. the level index has
reached the stored level count.  (`rootGuardState_flag_iff` gives that reading.) -/
def AFor_for_2268004712116198193 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₉ = Ok evm store → (Ok evm store)["split_expr_4"]!! = 0

/-- Loop body: break if the levels are exhausted, take the index's parity, fold one
level, advance to the parent, and store the new node. -/
def ABody_for_2268004712116198193 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec A_if_2425414531525476249 (rootGuardState s₀) s₁ ∧
    ∃ s₂, Spec (A_mod_uint256 "split_expr_5" (s₁["var_index"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec A_switch_8961670722464898128 s₂ s₃ ∧
        ∃ s₄, Spec A_block_5022472617119597648 s₃ s₄ ∧
          ∃ s₅, Spec A_block_2896862189596047701 s₄ s₅ ∧
            s₉ = s₅

/-- The flag is zero exactly when the level index has reached the stored count. -/
lemma rootGuardState_flag_iff {s : State} (hok : isOk s) :
    (rootGuardState s)["split_expr_4"]!! = 0 ↔
      ¬ (s["var_i"]!! < Clear.EVMState.sload s.evm 0) := by
  unfold rootGuardState
  rw [lookup_insert' (by simpa [isOk_insert] using hok),
    lookup_insert_of_ne (by decide), lookup_insert' hok]
  by_cases hlt : s["var_i"]!! < Clear.EVMState.sload s.evm 0
  · simp [hlt]
  · simp [hlt]

lemma for_2268004712116198193_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_2268004712116198193_post_concrete_of_code s₀ s₉ →
  Spec APost_for_2268004712116198193 s₀ s₉ := by
  unfold for_2268004712116198193_post_concrete_of_code APost_for_2268004712116198193
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma for_2268004712116198193_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_2268004712116198193_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_2268004712116198193 s₀ s₉ := by
  unfold for_2268004712116198193_body_concrete_of_code ABody_for_2268004712116198193 rootGuardState
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq.symm⟩

/-- Vacuous: the loop condition is the literal `1`. -/
lemma AZero_for_2268004712116198193 : ∀ s₀, isOk s₀ → ACond_for_2268004712116198193 (👌 s₀) = 0 → AFor_for_2268004712116198193 s₀ s₀ := by
  intro s₀ _hok hcond
  unfold ACond_for_2268004712116198193 at hcond
  exact absurd hcond (by decide)

lemma AOk_for_2268004712116198193 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_2268004712116198193 s₀ = 0 → ABody_for_2268004712116198193 s₀ s₂ → APost_for_2268004712116198193 s₂ s₄ → Spec AFor_for_2268004712116198193 s₄ s₅ → AFor_for_2268004712116198193 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 h2 h5 _hcond _hbody hpost hspec
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have h4 : s₄ = (Ok e2 st2)⟦"var_i" ↦ ((Ok e2 st2)["var_i"]!! + 1)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    exact Spec_ok_unfold (P := AFor_for_2268004712116198193) (s := s₄) (s' := s₅) hok4 h5 hspec
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])

lemma AContinue_for_2268004712116198193 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_2268004712116198193 s₀ = 0 → ABody_for_2268004712116198193 s₀ s₂ → Spec APost_for_2268004712116198193 (🧟s₂) s₄ → Spec AFor_for_2268004712116198193 s₄ s₅ → AFor_for_2268004712116198193 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 _h2 _hcond _hbody _hpost hspec
  intro evm store hs
  have h5 : ¬ ❓ s₅ := by rw [hs]; simp [State.isOutOfFuel]
  rcases s₄ with ⟨e4, st4⟩ | _ | _
  · exact Spec_ok_unfold (P := AFor_for_2268004712116198193) (by simp [isOk]) h5 hspec evm store hs
  · exact absurd (hspec) (by rw [hs] at *; simp [Spec, State.isOutOfFuel])
  · exact absurd (hspec) (by rw [hs] at *; simp [Spec, State.isJump])

/-- **The main exit.**  The single break guard is the only way out, so either it fired
-- and the flag was zero, which is exactly `AFor` -- or the body ran to the end `Ok`,
contradicting `isBreak`. -/
lemma ABreak_for_2268004712116198193 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_2268004712116198193 s₀ = 0 → ABody_for_2268004712116198193 s₀ s₂ → AFor_for_2268004712116198193 s₀ (🧟s₂) := by
  intro s₀ sb h0 hb _hcond hbody
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := hbody
  rw [heq] at hb ⊢
  have h5nf : ¬ ❓ s₅ := by
    rcases s₅ with ⟨e, st⟩ | _ | c
    · simp [State.isOutOfFuel]
    · simp [State.isBreak] at hb
    · simp [State.isOutOfFuel]
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardState s₀) := by
    unfold rootGuardState; simp only [isOk_insert]; exact h0
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hf : (rootGuardState s₀)["split_expr_4"]!! = 0
  · have e1 : s₁ = 💔(rootGuardState s₀) := hg.1 hf
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj2 : isJump (.Break be bst) s₂ := Clear.isJump_of_Spec_of_isJump h₂ hj1
    have hj3 : isJump (.Break be bst) s₃ := Clear.isJump_of_Spec_of_isJump h₃ hj2
    have hj4 : isJump (.Break be bst) s₄ := Clear.isJump_of_Spec_of_isJump h₄ hj3
    rw [Clear.reviveJump_eq_of_Spec_of_isJump h₅ hj4,
      Clear.reviveJump_eq_of_Spec_of_isJump h₄ hj3,
      Clear.reviveJump_eq_of_Spec_of_isJump h₃ hj2,
      Clear.reviveJump_eq_of_Spec_of_isJump h₂ hj1, e1, Clear.reviveJump_setBreak hgc]
    intro evm store hs
    rw [← hs]
    exact hf
  · exfalso
    have e1 : s₁ = rootGuardState s₀ := hg.2 hf
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ := switch_8961670722464898128_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ := block_5022472617119597648_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have hs5 : isOk s₅ := block_2896862189596047701_isOk hs4 h5nf (Spec_ok_unfold hs4 h5nf h₅)
    exact not_isOk_of_isBreak hb hs5

lemma ALeave_for_2268004712116198193 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_2268004712116198193 s₀ = 0 → ABody_for_2268004712116198193 s₀ s₂ → AFor_for_2268004712116198193 s₀ s₂ := by
  intro s₀ s₂ _h0 h2 _hcond _hbody
  intro evm store hs
  rcases s₂ with _ | _ | c
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd hs (by simp)

end

end L2InteropCommitmentTree.Common
