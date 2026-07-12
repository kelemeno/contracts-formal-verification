import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7182708311549001418
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_8692170500034331446

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common 

def A_update_storage_value_bytes32_to_bytes32  (slot offset value : Literal) (s₀ s₉ : State) : Prop := update_storage_value_bytes32_to_bytes32_concrete_of_code.1  slot offset value s₀ s₉

lemma update_storage_value_bytes32_to_bytes32_abs_of_concrete {s₀ s₉ : State} { slot offset value} :
  Spec (update_storage_value_bytes32_to_bytes32_concrete_of_code.1  slot offset value) s₀ s₉ →
  Spec (A_update_storage_value_bytes32_to_bytes32  slot offset value) s₀ s₉ := by
  intro h
  simpa [A_update_storage_value_bytes32_to_bytes32] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
