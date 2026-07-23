import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr_5303
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_8102603259148870207_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_block_8102603259148870207 (s₀ s₉ : State) : Prop := block_8102603259148870207_concrete_of_code.1 s₀ s₉

lemma block_8102603259148870207_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8102603259148870207_concrete_of_code s₀ s₉ →
  Spec A_block_8102603259148870207 s₀ s₉ := by
  intro h
  simpa [A_block_8102603259148870207] using h

end

end L2InteropCommitmentTree.Common
