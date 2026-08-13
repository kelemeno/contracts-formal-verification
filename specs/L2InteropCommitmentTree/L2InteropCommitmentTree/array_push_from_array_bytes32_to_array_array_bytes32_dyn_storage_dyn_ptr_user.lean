import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4590714779410500988
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_228369243124659344
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_3779316958150250372
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_dataslot_array_array_bytes32_dyn_storage_dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_6561856544793224737

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Append a new INNER array holding one element** — the array-of-arrays push.

This is how the tree gains a level: the outer array's length goes up by one, and the new
inner array is created with length 1 and its single element written.

```
    oldLen := sload(array); reject oldLen ≥ 2^64        -- if_4590714779410500988
    sstore(array, oldLen + 1)                           -- outer length++
    slot, offset := storage_array_index_access(array, oldLen)
    reject offset ≠ 0                                   -- if_228369243124659344
    oldLen_1 := sload(slot); sstore(slot, 1)            -- inner length := 1
    clear elements 1 .. oldLen_1 of the inner array     -- if_3779316958150250372
    dstSlot := array_dataslot(slot); copy 1 word from srcPtr
```

The `oldLen_1` read and the zero-fill are what make reuse safe: the slot may hold a
STALE longer array from a previous life, and truncating to length 1 without clearing
would leave those elements readable.  Element 0 is not cleared because it is about to be
overwritten by the copy. -/
def A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr (array value0 : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["array", "value0"],[array, value0]⟧
  let g := f⟦"oldLen" ↦ Clear.EVMState.sload f.evm (f["array"]!!)⟧
  let gc := g⟦"split_expr_0" ↦ (decide (g["oldLen"]!! < 18446744073709551616)).toUInt256⟧
  ∃ s₁, Spec L2InteropCommitmentTree.Common.A_if_4590714779410500988 gc s₁ ∧
    (let inc := s₁⟦"split_expr_1" ↦ s₁["oldLen"]!! + 1⟧
     let st := inc🇪⟦Clear.EVMState.sstore s₁.evm (inc["array"]!!) (inc["split_expr_1"]!!)⟧
     ∃ s₂, Spec (A_storage_array_index_access_bytes32_dyn_ptr "slot" "offset"
         (st["array"]!!) (st["oldLen"]!!)) st s₂ ∧
       ∃ s₃, Spec L2InteropCommitmentTree.Common.A_if_228369243124659344 s₂ s₃ ∧
         (let ld := s₃⟦"oldLen_1" ↦ Clear.EVMState.sload s₃.evm (s₃["slot"]!!)⟧
          -- the sstore takes the PRE-insert evm, as elsewhere in this generator
          let one := ld🇪⟦Clear.EVMState.sstore s₃.evm (ld["slot"]!!) 1⟧
          ∃ s₄, Spec L2InteropCommitmentTree.Common.A_if_3779316958150250372 one s₄ ∧
            (let src := s₄⟦"srcPtr" ↦ s₄["value0"]!!⟧
             ∃ s₅, Spec (A_array_dataslot_array_bytes32_dyn_storage_ptr "dstSlot"
                 (src["slot"]!!)) src s₅ ∧
               ∃ s₆, Spec L2InteropCommitmentTree.Common.AFor_for_6561856544793224737
                   (s₅⟦"i" ↦ 0⟧) s₆ ∧
                 s₉ = 🧟s₆🏪⟦s₀⟧)))

lemma array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_abs_of_concrete {s₀ s₉ : State} {array value0} :
  Spec (array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_concrete_of_code.1 array value0) s₀ s₉ →
  Spec (A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr array value0) s₀ s₉ := by
  unfold array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_concrete_of_code A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, heq.symm⟩

lemma array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_isOk {array value0 : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr array value0 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, _, s₂, _, s₃, _, s₄, _, s₅, _, s₆, _, heq⟩ := h
  subst heq
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_not_break {array value0 : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr array value0 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_isOk hnf h)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
