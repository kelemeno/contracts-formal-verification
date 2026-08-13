import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2014493949976689796

import generated.AtomicFlowManager.AtomicFlowManager.validator_assert_enum_LegState_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

/-- **The `LegState` validity assertion.**  Computes `lt(value, 4)` and hands it to
`if_2014493949976689796`, which panics (code 33, invalid enum) when it is zero.

No output parameters: the function is a pure assertion, so the state advances only
by the guard and the return restores the caller's store.  A caller that gets past
this call knows the byte it read is one of the four `LegState` values. -/
def A_validator_assert_enum_LegState (value : Literal) (s₀ s₉ : State) : Prop :=
  ∃ ss, Spec AtomicFlowManager.Common.A_if_2014493949976689796
      (s₀☎️⟦["value"],[value]⟧⟦"split_expr_0" ↦
        (decide ((s₀☎️⟦["value"],[value]⟧)["value"]!! < 4)).toUInt256⟧) ss ∧
    s₉ = 🧟ss🏪⟦s₀⟧

lemma validator_assert_enum_LegState_abs_of_concrete {s₀ s₉ : State} {value} :
  Spec (validator_assert_enum_LegState_concrete_of_code.1 value) s₀ s₉ →
  Spec (A_validator_assert_enum_LegState value) s₀ s₉ := by
  unfold validator_assert_enum_LegState_concrete_of_code A_validator_assert_enum_LegState
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨ss, hg, heq⟩ := hc
  exact ⟨ss, hg, heq.symm⟩

/-- Output is `Ok`: the return is `🧟`-shaped. -/
lemma validator_assert_enum_LegState_isOk {value : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_validator_assert_enum_LegState value s₀ s₉) : isOk s₉ := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simp only [isOutOfFuel_setStore', isOutOfFuel_reviveJump']
  exact hoo

lemma validator_assert_enum_LegState_not_break {value : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_validator_assert_enum_LegState value s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (validator_assert_enum_LegState_isOk hnf h)

end

end generated.AtomicFlowManager.AtomicFlowManager
