import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_1966118315202180062
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation_5209_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_finalize_allocation_5209  (memPtr : Literal) (s₀ s₉ : State) : Prop := finalize_allocation_5209_concrete_of_code.1  memPtr s₀ s₉

lemma finalize_allocation_5209_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (finalize_allocation_5209_concrete_of_code.1  memPtr) s₀ s₉ →
  Spec (A_finalize_allocation_5209  memPtr) s₀ s₉ := by
  intro h
  simpa [A_finalize_allocation_5209] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
