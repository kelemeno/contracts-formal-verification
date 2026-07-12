import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_2896862189596047701_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_block_2896862189596047701 (s₀ s₉ : State) : Prop := block_2896862189596047701_concrete_of_code.1 s₀ s₉

lemma block_2896862189596047701_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2896862189596047701_concrete_of_code s₀ s₉ →
  Spec A_block_2896862189596047701 s₀ s₉ := by
  intro h
  simpa [A_block_2896862189596047701] using h

end

end L2InteropCommitmentTree.Common
