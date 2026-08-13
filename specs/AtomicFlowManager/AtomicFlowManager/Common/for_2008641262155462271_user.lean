import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3176736767708389615
import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7848
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8934115175442537836
import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32
import generated.AtomicFlowManager.AtomicFlowManager.read_from_storage_split_offset_enum_LegState
import generated.AtomicFlowManager.AtomicFlowManager.validator_assert_enum_LegState
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2726844535930192361
import generated.AtomicFlowManager.AtomicFlowManager.update_storage_value_offset_enum_LegState_to_enum_LegState

import generated.AtomicFlowManager.AtomicFlowManager.Common.for_2008641262155462271_gen


namespace AtomicFlowManager.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

/-- Loop condition: `lt(var_i, expr_383_length)`. -/
def ACond_for_2008641262155462271 (s₀ : State) : Literal :=
  fromBool (s₀["var_i"]!! < s₀["expr_383_length"]!!)

/-- Loop post: `var_i := add(var_i, 1)`. -/
def APost_for_2008641262155462271 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"var_i" ↦ ((Ok evm store)["var_i"]!! + 1)⟧

/-- Loop postcondition: on normal exit the cursor has REACHED the bound, so the body
ran for every step. A property of `s₉` alone -- that is what lets the closure lemmas
thread it through unchanged, and it is sound because `expr_383_length` is untouched by body
and post. -/
def AFor_for_2008641262155462271 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₉ = Ok evm store → ¬ ((Ok evm store)["var_i"]!! < (Ok evm store)["expr_383_length"]!!)

/-- Loop body: read leg `i` and its state, skip unless it is state 1, then derive the
leg's slot again and write state 2.  The `log3` the Yul emits after the write does not
appear: Clear models LOG as a no-op returning the state unchanged. -/
def ABody_for_2008641262155462271 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec A_block_3176736767708389615 s₀ s₁ ∧
    ∃ s₂, Spec A_block_8934115175442537836 s₁ s₂ ∧
      ∃ s₃, Spec A_if_2726844535930192361 s₂ s₃ ∧
        ∃ s₄, Spec (A_mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7848 "split_expr_10" (s₃["value_3"]!!)) s₃ s₄ ∧
          ∃ s₅, Spec (A_mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32 "split_expr_11" (s₄["split_expr_10"]!!) (s₄["value_5"]!!)) s₄ s₅ ∧
            ∃ s₆, Spec (A_update_storage_value_offset_enum_LegState_to_enum_LegState (s₅["split_expr_11"]!!)) s₅ s₆ ∧
              s₉ = s₆

lemma for_2008641262155462271_cond_abs_of_code {s₀ fuel} : eval fuel for_2008641262155462271_cond (s₀) = (s₀, ACond_for_2008641262155462271 (s₀)) := by
  unfold eval ACond_for_2008641262155462271
  simp [for_2008641262155462271_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_2008641262155462271_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_2008641262155462271_post_concrete_of_code s₀ s₉ →
  Spec APost_for_2008641262155462271 s₀ s₉ := by
  unfold for_2008641262155462271_post_concrete_of_code APost_for_2008641262155462271
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma AZero_for_2008641262155462271 : ∀ s₀, isOk s₀ → ACond_for_2008641262155462271 (👌 s₀) = 0 → AFor_for_2008641262155462271 s₀ s₀ := by
  intro s₀ hok hcond
  unfold AFor_for_2008641262155462271 ACond_for_2008641262155462271 at *
  intro evm store hs
  subst hs
  intro hlt
  -- the guard evaluated to 0, so the comparison it decided was false
  simp only [State.mkOk] at hcond
  simp [fromBool, Bool.toUInt256, hlt] at hcond

lemma AOk_for_2008641262155462271 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_2008641262155462271 s₀ = 0 → ABody_for_2008641262155462271 s₀ s₂ → APost_for_2008641262155462271 s₂ s₄ → Spec AFor_for_2008641262155462271 s₄ s₅ → AFor_for_2008641262155462271 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 h2 h5 _hcond _hbody hpost hspec
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have h4 : s₄ = (Ok e2 st2)⟦"var_i" ↦ ((Ok e2 st2)["var_i"]!! + 1)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    -- name the implicits: `AFor` ignores its first argument, but unification does not know that
    exact Spec_ok_unfold (P := AFor_for_2008641262155462271) (s := s₄) (s' := s₅) hok4 h5 hspec
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])

lemma AContinue_for_2008641262155462271 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_2008641262155462271 s₀ = 0 → ABody_for_2008641262155462271 s₀ s₂ → Spec APost_for_2008641262155462271 (🧟s₂) s₄ → Spec AFor_for_2008641262155462271 s₄ s₅ → AFor_for_2008641262155462271 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 _h2 _hcond _hbody _hpost hspec
  intro evm store hs
  -- no reasoning about the continue state is needed: case on s₄ and read Spec off its definition
  have h5 : ¬ ❓ s₅ := by rw [hs]; simp [State.isOutOfFuel]
  rcases s₄ with ⟨e4, st4⟩ | _ | c4
  · exact Spec_ok_unfold (P := AFor_for_2008641262155462271) (s := Ok e4 st4) (s' := s₅) (by simp [isOk]) h5 hspec evm store hs
  · exact absurd (by simpa [Spec] using hspec) h5
  · have hj : s₅.isJump c4 := by simpa [Spec] using hspec
    rw [hs] at hj
    exact absurd hj (by simp [State.isJump])

lemma ALeave_for_2008641262155462271 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_2008641262155462271 s₀ = 0 → ABody_for_2008641262155462271 s₀ s₂ → AFor_for_2008641262155462271 s₀ s₂ := by
  intro s₀ s₂ _h0 h2 _hcond _hbody
  -- a leave state is a Checkpoint, so the postcondition's hypothesis is unsatisfiable
  intro evm store hs
  rcases s₂ with _ | _ | c
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd hs (by simp)

lemma for_2008641262155462271_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_2008641262155462271_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_2008641262155462271 s₀ s₉ := by
  unfold for_2008641262155462271_body_concrete_of_code ABody_for_2008641262155462271
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, heq.symm⟩

/-- **No `break` can leave this body** — and unlike the sortedness loops, showing it
needs BOTH non-`Ok` paths, because the skip guard continues rather than reverting:

- skip taken: the guard yields a `Continue` checkpoint, and every later step carries
  that same checkpoint forward (`isJump_of_Spec_of_isJump`), so the body's output is a
  `Continue` — not a `Break`;
- skip not taken: the chain stays `Ok` through both slot derivations and the write.

`isBreak` supplies `¬ ❓`, which walks backwards and lets each intermediate be assumed
well-behaved. -/
lemma ABreak_for_2008641262155462271 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_2008641262155462271 s₀ = 0 → ABody_for_2008641262155462271 s₀ s₂ → AFor_for_2008641262155462271 s₀ (🧟s₂) := by
  intro s₀ sb h0 hb _hcond hbody
  exfalso
  have hnfb : ¬ ❓ sb := by
    rcases sb with ⟨e, st⟩ | _ | c
    · simp [State.isOutOfFuel]
    · exact absurd hb (by simp [State.isBreak])
    · simp [State.isOutOfFuel]
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, heq⟩ := hbody
  rw [heq] at hb hnfb
  have h5nf : ¬ ❓ s₅ := fun hoo => hnfb (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₆ hoo)
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ := block_3176736767708389615_isOk h0 h1nf (Spec_ok_unfold h0 h1nf h₁)
  have hs2 : isOk s₂ := block_8934115175442537836_isOk hs1 h2nf (Spec_ok_unfold hs1 h2nf h₂)
  have hg := Spec_ok_unfold hs2 h3nf h₃
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · by_cases hflag : (Ok e2 st2)["split_expr_9"]!! = 0
    · have hj3 : isJump (.Continue e2 st2) s₃ := by
        rw [hg.1 hflag]; simp [State.setContinue, State.isJump]
      exact Clear.not_isBreak_of_isJump_Continue
        (Clear.isJump_of_Spec_of_isJump h₆
          (Clear.isJump_of_Spec_of_isJump h₅
            (Clear.isJump_of_Spec_of_isJump h₄ hj3))) hb
    · have h3ok : isOk s₃ := by rw [hg.2 hflag]; simp [isOk]
      have hs4 : isOk s₄ := mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7848_isOk h4nf (Spec_ok_unfold h3ok h4nf h₄)
      have hs5 : isOk s₅ := mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_isOk h5nf (Spec_ok_unfold hs4 h5nf h₅)
      have hs6 : isOk s₆ := update_storage_value_offset_enum_LegState_to_enum_LegState_isOk hnfb (Spec_ok_unfold hs5 hnfb h₆)
      exact not_isOk_of_isBreak hb hs6
  · exact absurd hs2 (by simp [isOk])
  · exact absurd hs2 (by simp [isOk])

end

end AtomicFlowManager.Common
