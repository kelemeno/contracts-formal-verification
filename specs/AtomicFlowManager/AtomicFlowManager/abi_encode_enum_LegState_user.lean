import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2014493949976689796

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_enum_LegState_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

/-- **Encode a `LegState` into a revert payload**: range-check, then `mstore(pos, value)`.

The same `< 4` check `validator_assert_enum_LegState` uses, sharing its guard
(`if_2014493949976689796`, Panic code 33).  So even the ERROR path refuses to emit a
`LegState` outside `0..3`: an out-of-range value panics rather than being reported. -/
def A_abi_encode_enum_LegState (value pos : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["value", "pos"],[value, pos]⟧
  let g := f⟦"split_expr_0" ↦ (decide (f["value"]!! < 4)).toUInt256⟧
  ∃ ss, Spec AtomicFlowManager.Common.A_if_2014493949976689796 g ss ∧
    s₉ = 🧟(ss🇪⟦Clear.EVMState.mstore ss.evm (ss["pos"]!!) (ss["value"]!!)⟧)🏪⟦s₀⟧

lemma abi_encode_enum_LegState_abs_of_concrete {s₀ s₉ : State} {value pos} :
  Spec (abi_encode_enum_LegState_concrete_of_code.1 value pos) s₀ s₉ →
  Spec (A_abi_encode_enum_LegState value pos) s₀ s₉ := by
  unfold abi_encode_enum_LegState_concrete_of_code A_abi_encode_enum_LegState
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨ss, hg, heq⟩ := hc
  exact ⟨ss, hg, heq.symm⟩

lemma abi_encode_enum_LegState_isOk {value pos : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_abi_encode_enum_LegState value pos s₀ s₉) : isOk s₉ := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump', isOutOfFuel_setEvm'] using hoo

lemma abi_encode_enum_LegState_not_break {value pos : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_abi_encode_enum_LegState value pos s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (abi_encode_enum_LegState_isOk hnf h)

end

end generated.AtomicFlowManager.AtomicFlowManager
