import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_uncheckedInc
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_6359192996994294239_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_block_6359192996994294239 (s₀ s₉ : State) : Prop := block_6359192996994294239_concrete_of_code.1 s₀ s₉

lemma block_6359192996994294239_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6359192996994294239_concrete_of_code s₀ s₉ →
  Spec A_block_6359192996994294239 s₀ s₉ := by
  intro h
  simpa [A_block_6359192996994294239] using h

end

end L2InteropCommitmentTree.Common
