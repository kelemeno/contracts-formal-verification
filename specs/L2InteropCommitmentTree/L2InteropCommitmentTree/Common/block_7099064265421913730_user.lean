import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_allocation_size_array_bytes32_dyn

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7099064265421913730_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_block_7099064265421913730 (s₀ s₉ : State) : Prop := block_7099064265421913730_concrete_of_code.1 s₀ s₉

lemma block_7099064265421913730_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7099064265421913730_concrete_of_code s₀ s₉ →
  Spec A_block_7099064265421913730 s₀ s₉ := by
  intro h
  simpa [A_block_7099064265421913730] using h

end

end L2InteropCommitmentTree.Common
