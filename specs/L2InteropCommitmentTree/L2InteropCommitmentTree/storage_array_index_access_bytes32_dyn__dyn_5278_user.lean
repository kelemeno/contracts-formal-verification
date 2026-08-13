import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_6945705467323769142
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn_5278_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Address of element 0** of a dynamic storage array: the no-index specialisation.

```
    if iszero(sload(array)) { panic_error_0x32() }
    mstore(0, array); slot := keccak256(0, 32); offset := 0
```

Same layout rule as the indexed accessor -- elements start at `keccak(arraySlot)` --
but with no `+ index`, so this is element 0 and the bounds check degenerates to "the
array is non-empty". -/
def A_storage_array_index_access_bytes32_dyn__dyn_5278 (slot offset : Identifier) (array : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["array"],[array]⟧
  let g := f⟦"split_expr_0" ↦ Clear.EVMState.sload f.evm (f["array"]!!)⟧
  ∃ ss, Spec L2InteropCommitmentTree.Common.A_if_6945705467323769142 g ss ∧
    (let m := ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧
     let kk := Clear.State.multifill ["slot"] (primCall m .Keccak256 [0, 32]).2
       (primCall m .Keccak256 [0, 32]).1
     let of := kk⟦"offset" ↦ 0⟧
     s₉ = 🧟of🏪⟦s₀⟧⟦offset ↦ of["offset"]!!⟧⟦slot ↦ of["slot"]!!⟧)

lemma storage_array_index_access_bytes32_dyn__dyn_5278_abs_of_concrete {s₀ s₉ : State} {slot offset array} :
  Spec (storage_array_index_access_bytes32_dyn__dyn_5278_concrete_of_code.1 slot offset array) s₀ s₉ →
  Spec (A_storage_array_index_access_bytes32_dyn__dyn_5278 slot offset array) s₀ s₉ := by
  unfold storage_array_index_access_bytes32_dyn__dyn_5278_concrete_of_code A_storage_array_index_access_bytes32_dyn__dyn_5278
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨ss, hg, heq⟩ := hc
  exact ⟨ss, hg, heq.symm⟩

lemma storage_array_index_access_bytes32_dyn__dyn_5278_isOk {slot offset : Identifier} {array : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_storage_array_index_access_bytes32_dyn__dyn_5278 slot offset array s₀ s₉) : isOk s₉ := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  apply isOk_insert.mpr
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma storage_array_index_access_bytes32_dyn__dyn_5278_not_break {slot offset : Identifier} {array : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_storage_array_index_access_bytes32_dyn__dyn_5278 slot offset array s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (storage_array_index_access_bytes32_dyn__dyn_5278_isOk hnf h)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
