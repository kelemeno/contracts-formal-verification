import Clear.ReasoningPrinciple
import specs.KeccakClean
import specs.KeccakLowSlot
import specs.StorageFrame
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_801497109727252421
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_6033096439800527865
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_5792510925045852942
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **`finalize_allocation(memPtr, size)` — bump the free-memory pointer.**

Rounds `size` up to a word, adds it to `memPtr`, panics `0x41` if the result passes the
`2^64 - 1` ceiling or wraps below `memPtr`, and only then writes the new value to the
free pointer at memory offset 64.

The order is what matters: BOTH overflow tests happen before `mstore(64, …)`, so a
rejected allocation leaves the free pointer untouched. -/
def A_finalize_allocation (memPtr size : Literal) (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec L2InteropCommitmentTree.Common.A_block_801497109727252421
      (s₀☎️⟦["memPtr", "size"],[memPtr, size]⟧) s₁ ∧
    ∃ s₂, Spec L2InteropCommitmentTree.Common.A_block_6033096439800527865 s₁ s₂ ∧
      ∃ s₃, Spec L2InteropCommitmentTree.Common.A_if_5792510925045852942 s₂ s₃ ∧
        s₉ = 🧟(s₃🇪⟦Clear.EVMState.mstore s₃.evm 64 (s₃["newFreePtr"]!!)⟧)🏪⟦s₀⟧

lemma finalize_allocation_abs_of_concrete {s₀ s₉ : State} {memPtr size} :
  Spec (finalize_allocation_concrete_of_code.1 memPtr size) s₀ s₉ →
  Spec (A_finalize_allocation memPtr size) s₀ s₉ := by
  unfold finalize_allocation_concrete_of_code A_finalize_allocation
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

lemma finalize_allocation_isOk {memPtr size : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_finalize_allocation memPtr size s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, _, s₂, _, s₃, _, heq⟩ := h
  subst heq
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump', isOutOfFuel_setEvm'] using hoo

lemma finalize_allocation_not_break {memPtr size : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_finalize_allocation memPtr size s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (finalize_allocation_isOk hnf h)

/-! ### The allocator's frames

`finalize_allocation` rounds the size, checks the two overflow conditions, and writes the
new free pointer to memory word 64.  Memory only -- so storage, window, flag and accounts
all cross it untouched, and each frame is the corresponding `mstore` lemma applied once. -/

private lemma fin_chain {s₀ s₉ : State} (hnf : ¬ ❓ s₉) {s₁ s₂ s₃ : State}
    (h₂ : Spec L2InteropCommitmentTree.Common.A_block_6033096439800527865 s₁ s₂)
    (h₃ : Spec L2InteropCommitmentTree.Common.A_if_5792510925045852942 s₂ s₃)
    (heq : s₉ = 🧟(s₃🇪⟦Clear.EVMState.mstore s₃.evm 64 (s₃["newFreePtr"]!!)⟧)🏪⟦s₀⟧) :
    ¬ ❓ s₃ ∧ ¬ ❓ s₂ ∧ ¬ ❓ s₁ := by
  have h3nf : ¬ ❓ s₃ := by
    intro hoo; apply hnf; rw [heq]
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump', isOutOfFuel_setEvm'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  exact ⟨h3nf, h2nf, fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)⟩

/-- The three states in the chain are `Ok`, given an `Ok` start. -/
private lemma fin_ok {memPtr size : Literal} {s₀ : State} (hok : isOk s₀) {s₁ s₂ s₃ : State}
    (h₁ : Spec L2InteropCommitmentTree.Common.A_block_801497109727252421
      (s₀☎️⟦["memPtr", "size"],[memPtr, size]⟧) s₁)
    (h₂ : Spec L2InteropCommitmentTree.Common.A_block_6033096439800527865 s₁ s₂)
    (h₃ : Spec L2InteropCommitmentTree.Common.A_if_5792510925045852942 s₂ s₃)
    (h1nf : ¬ ❓ s₁) (h2nf : ¬ ❓ s₂) (h3nf : ¬ ❓ s₃) :
    isOk s₁ ∧ isOk s₂ ∧ isOk s₃ := by
  have hfok : isOk (s₀☎️⟦["memPtr", "size"],[memPtr, size]⟧) := isOk_initcall_of_isOk hok
  have hs1 : isOk s₁ := L2InteropCommitmentTree.Common.block_801497109727252421_isOk hfok
    (Spec_ok_unfold hfok h1nf h₁)
  have hs2 : isOk s₂ := L2InteropCommitmentTree.Common.block_6033096439800527865_isOk hs1
    (Spec_ok_unfold hs1 h2nf h₂)
  exact ⟨hs1, hs2, L2InteropCommitmentTree.Common.if_5792510925045852942_isOk hs2 h3nf
    (Spec_ok_unfold hs2 h3nf h₃)⟩

/-- The evm the allocator leaves behind: the caller's, with word 64 rewritten. -/
private lemma fin_evm {memPtr size : Literal} {s₀ s₃ : State} (hok : isOk s₀) (hs3 : isOk s₃)
    {s₁ s₂ : State}
    (h₁ : Spec L2InteropCommitmentTree.Common.A_block_801497109727252421
      (s₀☎️⟦["memPtr", "size"],[memPtr, size]⟧) s₁)
    (h₂ : Spec L2InteropCommitmentTree.Common.A_block_6033096439800527865 s₁ s₂)
    (h₃ : Spec L2InteropCommitmentTree.Common.A_if_5792510925045852942 s₂ s₃)
    (h1nf : ¬ ❓ s₁) (h2nf : ¬ ❓ s₂) (h3nf : ¬ ❓ s₃) :
    (🧟(s₃🇪⟦Clear.EVMState.mstore s₃.evm 64 (s₃["newFreePtr"]!!)⟧)🏪⟦s₀⟧).evm
      = Clear.EVMState.mstore s₃.evm 64 (s₃["newFreePtr"]!!) := by
  rw [evm_setStore, Clear.evm_reviveJump_of_isOk (by simp only [isOk_setEvm]; exact hs3),
    Clear.evm_setEvm_of_isOk hs3]

/-- **STORAGE FRAME.**  The allocator writes memory only. -/
lemma finalize_allocation_sload {memPtr size : Literal} {q : UInt256} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_finalize_allocation memPtr size s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  obtain ⟨h3nf, h2nf, h1nf⟩ := fin_chain hnf h₂ h₃ heq
  obtain ⟨hs1, hs2, hs3⟩ := fin_ok hok h₁ h₂ h₃ h1nf h2nf h3nf
  have hfok : isOk (s₀☎️⟦["memPtr", "size"],[memPtr, size]⟧) := isOk_initcall_of_isOk hok
  rw [heq, fin_evm hok hs3 h₁ h₂ h₃ h1nf h2nf h3nf, Clear.StorageFrame.sload_mstore,
    L2InteropCommitmentTree.Common.if_5792510925045852942_sload hs2 h3nf
      (Spec_ok_unfold hs2 h3nf h₃),
    L2InteropCommitmentTree.Common.block_6033096439800527865_evm
      (Spec_ok_unfold hs1 h2nf h₂),
    L2InteropCommitmentTree.Common.block_801497109727252421_evm
      (Spec_ok_unfold hfok h1nf h₁),
    Clear.evm_initcall hok]

/-- **KECCAK WINDOW.** -/
lemma finalize_allocation_config {memPtr size : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_finalize_allocation memPtr size s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  obtain ⟨h3nf, h2nf, h1nf⟩ := fin_chain hnf h₂ h₃ heq
  obtain ⟨hs1, hs2, hs3⟩ := fin_ok hok h₁ h₂ h₃ h1nf h2nf h3nf
  have hfok : isOk (s₀☎️⟦["memPtr", "size"],[memPtr, size]⟧) := isOk_initcall_of_isOk hok
  have e1 : s₁.evm = s₀.evm := by
    rw [L2InteropCommitmentTree.Common.block_801497109727252421_evm
      (Spec_ok_unfold hfok h1nf h₁), Clear.evm_initcall hok]
  have e2 : s₂.evm = s₁.evm :=
    L2InteropCommitmentTree.Common.block_6033096439800527865_evm (Spec_ok_unfold hs1 h2nf h₂)
  obtain ⟨hR3, hC3⟩ := L2InteropCommitmentTree.Common.if_5792510925045852942_config hs2 h3nf
    (by rw [e2, e1]; exact hR) (by rw [e2, e1]; exact hC) (Spec_ok_unfold hs2 h3nf h₃)
  rw [heq, fin_evm hok hs3 h₁ h₂ h₃ h1nf h2nf h3nf]
  exact ⟨Clear.StorageFrame.rangeInWindow_mstore hR3,
    Clear.StorageFrame.cachedInWindow_mstore hC3⟩

/-- **CLEAN FLAG.**  Nothing here hashes. -/
lemma finalize_allocation_clean {memPtr size : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_finalize_allocation memPtr size s₀ s₉) :
    Clear.KeccakClean.Clean s₉.evm ↔ Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  obtain ⟨h3nf, h2nf, h1nf⟩ := fin_chain hnf h₂ h₃ heq
  obtain ⟨hs1, hs2, hs3⟩ := fin_ok hok h₁ h₂ h₃ h1nf h2nf h3nf
  have hfok : isOk (s₀☎️⟦["memPtr", "size"],[memPtr, size]⟧) := isOk_initcall_of_isOk hok
  rw [heq, fin_evm hok hs3 h₁ h₂ h₃ h1nf h2nf h3nf, Clear.KeccakClean.clean_mstore,
    L2InteropCommitmentTree.Common.if_5792510925045852942_clean hs2 h3nf
      (Spec_ok_unfold hs2 h3nf h₃),
    L2InteropCommitmentTree.Common.block_6033096439800527865_evm
      (Spec_ok_unfold hs1 h2nf h₂),
    L2InteropCommitmentTree.Common.block_801497109727252421_evm
      (Spec_ok_unfold hfok h1nf h₁),
    Clear.evm_initcall hok]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
