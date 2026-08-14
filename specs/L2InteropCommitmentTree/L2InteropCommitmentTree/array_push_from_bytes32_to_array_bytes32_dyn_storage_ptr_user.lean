import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4590714779410500988
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Append to a dynamic storage array** — the deployed `push`.

```
    oldLen := sload(array)
    if iszero(lt(oldLen, 2^64)) { panic_error_0x41() }
    sstore(array, add(oldLen, 1))                       -- length := oldLen + 1
    slot, offset := storage_array_index_access(array, oldLen)
    update_storage_value_bytes32_to_bytes32(slot, offset, value0)
```

The shape gives the frame property the tree work needs: the length slot is set to
`oldLen + 1`, and the element write goes to the address of index `oldLen` — the
slot that was one PAST the end before this call.  No other slot is touched, and the
index written is not a caller argument but the length just read.

Note the ORDER: the length is incremented BEFORE the element is written, so the
bounds check inside `storage_array_index_access` (`index < sload(array)`) sees the
new length and admits `oldLen`.  Had the write come first, that check would reject
the very element being appended. -/
def A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr (array value0 : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["array", "value0"],[array, value0]⟧
  let g := f⟦"oldLen" ↦ Clear.EVMState.sload f.evm (f["array"]!!)⟧
  let gc := g⟦"split_expr_0" ↦ (decide (g["oldLen"]!! < 18446744073709551616)).toUInt256⟧
  ∃ s₁, Spec L2InteropCommitmentTree.Common.A_if_4590714779410500988 gc s₁ ∧
    (let inc := s₁⟦"split_expr_1" ↦ s₁["oldLen"]!! + 1⟧
     let st := inc🇪⟦Clear.EVMState.sstore s₁.evm (inc["array"]!!) (inc["split_expr_1"]!!)⟧
     ∃ s₂, Spec (A_storage_array_index_access_bytes32_dyn_ptr "slot" "offset"
         (st["array"]!!) (st["oldLen"]!!)) st s₂ ∧
       ∃ s₃, Spec (A_update_storage_value_bytes32_to_bytes32
           (s₂["slot"]!!) (s₂["offset"]!!) (s₂["value0"]!!)) s₂ s₃ ∧
         s₉ = 🧟s₃🏪⟦s₀⟧)

lemma array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_abs_of_concrete {s₀ s₉ : State} {array value0} :
  Spec (array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_concrete_of_code.1 array value0) s₀ s₉ →
  Spec (A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0) s₀ s₉ := by
  unfold array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_concrete_of_code A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

/-- Output is `Ok`: the return is `🧟`-shaped. -/
lemma array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_isOk {array value0 : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, _, s₂, _, s₃, _, heq⟩ := h
  subst heq
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_not_break {array value0 : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_isOk hnf h)


/-- The callee state after `initcall` and the length read -- `Ok`, and its evm is the
caller's, which is what puts the push's hypotheses in closed form over `s₀`. -/
lemma array_push_pre_evm {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    ((s₀☎️⟦["array", "value0"],[array, value0]⟧)⟦"oldLen" ↦
      Clear.EVMState.sload (s₀☎️⟦["array", "value0"],[array, value0]⟧).evm
        ((s₀☎️⟦["array", "value0"],[array, value0]⟧)["array"]!!)⟧).evm = s₀.evm := by
  simp only [evm_insert]
  exact Clear.evm_initcall hok

/-- The array argument, read back inside the callee. -/
lemma array_push_pre_array {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    (s₀☎️⟦["array", "value0"],[array, value0]⟧)["array"]!! = array :=
  Clear.lookup_initcall_fst hok

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
