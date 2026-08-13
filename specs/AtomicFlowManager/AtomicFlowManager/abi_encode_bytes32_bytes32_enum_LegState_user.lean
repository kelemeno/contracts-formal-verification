import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_enum_LegState

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_bytes32_bytes32_enum_LegState_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- **Three-argument revert payload**: `(bytes32, bytes32, LegState)`.

```
    tail := 100
    mstore(4, value0); mstore(36, value1)
    abi_encode_enum_LegState(value2, 68)
```

Layout: 4-byte selector, then three words at 4, 36, 68, for 100 bytes total.  The third
goes through `abi_encode_enum_LegState`, so it is range-checked rather than stored raw --
this is the payload of `ManagerLegNotRevertable(bytes32,bytes32,uint8)`. -/
def A_abi_encode_bytes32_bytes32_enum_LegState (tail : Identifier) (value0 value1 value2 : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["value0", "value1", "value2"],[value0, value1, value2]⟧
  let t := f⟦"tail" ↦ 100⟧
  let m1 := t🇪⟦Clear.EVMState.mstore t.evm 4 (t["value0"]!!)⟧
  let m2 := m1🇪⟦Clear.EVMState.mstore m1.evm 36 (m1["value1"]!!)⟧
  ∃ ss, Spec (A_abi_encode_enum_LegState (m2["value2"]!!) 68) m2 ss ∧
    s₉ = 🧟ss🏪⟦s₀⟧⟦tail ↦ ss["tail"]!!⟧

lemma abi_encode_bytes32_bytes32_enum_LegState_abs_of_concrete {s₀ s₉ : State} {tail value0 value1 value2} :
  Spec (abi_encode_bytes32_bytes32_enum_LegState_concrete_of_code.1 tail value0 value1 value2) s₀ s₉ →
  Spec (A_abi_encode_bytes32_bytes32_enum_LegState tail value0 value1 value2) s₀ s₉ := by
  unfold abi_encode_bytes32_bytes32_enum_LegState_concrete_of_code A_abi_encode_bytes32_bytes32_enum_LegState
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨ss, he, heq⟩ := hc
  exact ⟨ss, he, heq.symm⟩

lemma abi_encode_bytes32_bytes32_enum_LegState_isOk {tail : Identifier} {value0 value1 value2 : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_abi_encode_bytes32_bytes32_enum_LegState tail value0 value1 value2 s₀ s₉) : isOk s₉ := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma abi_encode_bytes32_bytes32_enum_LegState_not_break {tail : Identifier} {value0 value1 value2 : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_abi_encode_bytes32_bytes32_enum_LegState tail value0 value1 value2 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (abi_encode_bytes32_bytes32_enum_LegState_isOk hnf h)

end

end generated.AtomicFlowManager.AtomicFlowManager
