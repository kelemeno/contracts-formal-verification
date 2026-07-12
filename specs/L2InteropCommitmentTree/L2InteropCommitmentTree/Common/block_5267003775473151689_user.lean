import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.allocate_memory
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_5267003775473151689_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_block_5267003775473151689 (s₀ s₉ : State) : Prop := block_5267003775473151689_concrete_of_code.1 s₀ s₉

lemma block_5267003775473151689_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5267003775473151689_concrete_of_code s₀ s₉ →
  Spec A_block_5267003775473151689 s₀ s₉ := by
  intro h
  simpa [A_block_5267003775473151689] using h

end

end L2InteropCommitmentTree.Common
