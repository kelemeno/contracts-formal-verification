import Clear.ReasoningPrinciple
import specs.KeccakClean
import specs.KeccakLowSlot
import specs.StorageFrame
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.allocate_memory_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **`allocate_memory(size)` — the free pointer, then finalize.**

`memPtr := mload(64)` reads the current free-memory pointer and hands it to
`finalize_allocation`, which does the rounding, the overflow checks, and the write-back.
So the pointer this returns is the OLD free pointer -- the start of the region just
reserved -- and the checks that could reject the allocation all happen inside the call. -/
def A_allocate_memory (memPtr : Identifier) (size : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["size"],[size]⟧
  let m := f⟦"memPtr" ↦ Clear.EVMState.mload f.evm 64⟧
  ∃ s, Spec (A_finalize_allocation (m["memPtr"]!!) (m["size"]!!)) m s ∧
    s₉ = 🧟s🏪⟦s₀⟧⟦memPtr ↦ s["memPtr"]!!⟧

lemma allocate_memory_abs_of_concrete {s₀ s₉ : State} {memPtr size} :
  Spec (allocate_memory_concrete_of_code.1 memPtr size) s₀ s₉ →
  Spec (A_allocate_memory memPtr size) s₀ s₉ := by
  unfold allocate_memory_concrete_of_code A_allocate_memory
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hs, heq⟩ := hc
  exact ⟨s, hs, heq.symm⟩

lemma allocate_memory_isOk {memPtr : Identifier} {size : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_allocate_memory memPtr size s₀ s₉) : isOk s₉ := by
  obtain ⟨s, _, heq⟩ := h
  subst heq
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma allocate_memory_not_break {memPtr : Identifier} {size : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_allocate_memory memPtr size s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (allocate_memory_isOk hnf h)

/-! ### `allocate_memory`'s frames

A bump allocator: read the free pointer, hand it back, advance it.  Memory only, so the
three frames below are `finalize_allocation`'s composed with two evm-preserving wrappers. -/

/-- The state the allocator hands to `finalize_allocation`. -/
private def allocIn (size : Literal) (s₀ : State) : State :=
  let f := s₀☎️⟦["size"],[size]⟧
  f⟦"memPtr" ↦ Clear.EVMState.mload f.evm 64⟧

private lemma allocIn_isOk {size : Literal} {s₀ : State} (hok : isOk s₀) :
    isOk (allocIn size s₀) := isOk_insert.mpr (isOk_initcall_of_isOk hok)

private lemma allocIn_evm {size : Literal} {s₀ : State} (hok : isOk s₀) :
    (allocIn size s₀).evm = s₀.evm := by
  simp only [allocIn, evm_insert]; exact Clear.evm_initcall hok

/-- **STORAGE FRAME.**  Allocation writes memory, never storage. -/
lemma allocate_memory_sload {memPtr : Identifier} {size : Literal} {q : UInt256}
    {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_allocate_memory memPtr size s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨s, hs, heq⟩ := h
  have hin := allocIn_isOk (size := size) hok
  have hine := allocIn_evm (size := size) hok
  have hsnf : ¬ ❓ s := by
    intro hoo; apply hnf; rw [heq]
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have hsok : isOk s := finalize_allocation_isOk hsnf (Spec_ok_unfold hin hsnf hs)
  rw [heq, evm_insert, evm_setStore, Clear.evm_reviveJump_of_isOk hsok,
    finalize_allocation_sload hin hsnf (Spec_ok_unfold hin hsnf hs), hine]

/-- **KECCAK WINDOW.** -/
lemma allocate_memory_config {memPtr : Identifier} {size : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_allocate_memory memPtr size s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨s, hs, heq⟩ := h
  have hin := allocIn_isOk (size := size) hok
  have hine := allocIn_evm (size := size) hok
  have hsnf : ¬ ❓ s := by
    intro hoo; apply hnf; rw [heq]
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have hsok : isOk s := finalize_allocation_isOk hsnf (Spec_ok_unfold hin hsnf hs)
  obtain ⟨hRs, hCs⟩ := finalize_allocation_config hin hsnf (by rw [hine]; exact hR)
    (by rw [hine]; exact hC) (Spec_ok_unfold hin hsnf hs)
  rw [heq, evm_insert, evm_setStore, Clear.evm_reviveJump_of_isOk hsok]
  exact ⟨hRs, hCs⟩

/-- **CLEAN FLAG.**  Allocation never hashes. -/
lemma allocate_memory_clean {memPtr : Identifier} {size : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_allocate_memory memPtr size s₀ s₉) :
    Clear.KeccakClean.Clean s₉.evm ↔ Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s, hs, heq⟩ := h
  have hin := allocIn_isOk (size := size) hok
  have hine := allocIn_evm (size := size) hok
  have hsnf : ¬ ❓ s := by
    intro hoo; apply hnf; rw [heq]
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have hsok : isOk s := finalize_allocation_isOk hsnf (Spec_ok_unfold hin hsnf hs)
  rw [heq, evm_insert, evm_setStore, Clear.evm_reviveJump_of_isOk hsok,
    finalize_allocation_clean hin hsnf (Spec_ok_unfold hin hsnf hs), hine]

/-- **FRAME.**  Only `memPtr` moves; the call restores everything else. -/
lemma allocate_memory_frame {memPtr : Identifier} {size : Literal} {v : Identifier}
    {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hv : v ≠ memPtr)
    (h : A_allocate_memory memPtr size s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  obtain ⟨s, _, heq⟩ := h
  subst heq
  have hrev : isOk (🧟 s) := by
    apply Clear.isOk_reviveJump_of_not_isOutOfFuel
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  rw [lookup_insert_of_ne hv, Clear.lookup_setStore hrev hok]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
