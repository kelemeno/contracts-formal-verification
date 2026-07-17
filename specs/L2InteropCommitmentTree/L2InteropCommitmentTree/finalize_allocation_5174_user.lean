import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_1966118315202180062
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation_5174_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_finalize_allocation_5174  (memPtr : Literal) (s₀ s₉ : State) : Prop := sorry

lemma finalize_allocation_5174_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (finalize_allocation_5174_concrete_of_code.1  memPtr) s₀ s₉ →
  Spec (A_finalize_allocation_5174  memPtr) s₀ s₉ := by
  unfold finalize_allocation_5174_concrete_of_code A_finalize_allocation_5174
  sorry

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
