import Clear.ReasoningPrinciple
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

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
