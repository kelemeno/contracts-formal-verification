import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_3014048436703836940
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_allocation_size_array_bytes32_dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7099064265421913730
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_6142610688382842835

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.allocate_and_zero_memory_array_array_bytes32_dyn_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_allocate_and_zero_memory_array_array_bytes32_dyn (memPtr : Identifier) (length : Literal) (s₀ s₉ : State) : Prop := allocate_and_zero_memory_array_array_bytes32_dyn_concrete_of_code.1 memPtr length s₀ s₉

lemma allocate_and_zero_memory_array_array_bytes32_dyn_abs_of_concrete {s₀ s₉ : State} {memPtr length} :
  Spec (allocate_and_zero_memory_array_array_bytes32_dyn_concrete_of_code.1 memPtr length) s₀ s₉ →
  Spec (A_allocate_and_zero_memory_array_array_bytes32_dyn memPtr length) s₀ s₉ := by
  intro h
  simpa [A_allocate_and_zero_memory_array_array_bytes32_dyn] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
