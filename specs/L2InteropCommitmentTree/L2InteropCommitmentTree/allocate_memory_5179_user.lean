import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.allocate_memory_5179_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_allocate_memory_5179 (memPtr : Identifier)  (s₀ s₉ : State) : Prop := allocate_memory_5179_concrete_of_code.1 memPtr s₀ s₉

lemma allocate_memory_5179_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_memory_5179_concrete_of_code.1 memPtr ) s₀ s₉ →
  Spec (A_allocate_memory_5179 memPtr ) s₀ s₉ := by
  intro h
  simpa [A_allocate_memory_5179] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
