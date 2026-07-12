import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_801497109727252421
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_6033096439800527865
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_5792510925045852942
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_finalize_allocation  (memPtr size : Literal) (s₀ s₉ : State) : Prop := finalize_allocation_concrete_of_code.1  memPtr size s₀ s₉

lemma finalize_allocation_abs_of_concrete {s₀ s₉ : State} { memPtr size} :
  Spec (finalize_allocation_concrete_of_code.1  memPtr size) s₀ s₉ →
  Spec (A_finalize_allocation  memPtr size) s₀ s₉ := by
  intro h
  simpa [A_finalize_allocation] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
