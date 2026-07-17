import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_5022472617119597648_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_block_5022472617119597648 (s₀ s₉ : State) : Prop := sorry

lemma block_5022472617119597648_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5022472617119597648_concrete_of_code s₀ s₉ →
  Spec A_block_5022472617119597648 s₀ s₉ := by
  sorry

end

end L2InteropCommitmentTree.Common
