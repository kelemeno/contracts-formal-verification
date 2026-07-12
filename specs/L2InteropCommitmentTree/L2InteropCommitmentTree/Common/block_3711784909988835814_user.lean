import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_3711784909988835814_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_block_3711784909988835814 (s₀ s₉ : State) : Prop := block_3711784909988835814_concrete_of_code.1 s₀ s₉

lemma block_3711784909988835814_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3711784909988835814_concrete_of_code s₀ s₉ →
  Spec A_block_3711784909988835814 s₀ s₉ := by
  intro h
  simpa [A_block_3711784909988835814] using h

end

end L2InteropCommitmentTree.Common
