import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2600721580863995212
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn_5219_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_storage_array_index_access_bytes32_dyn__dyn_5219 (slot offset : Identifier) (index : Literal) (s₀ s₉ : State) : Prop := storage_array_index_access_bytes32_dyn__dyn_5219_concrete_of_code.1 slot offset index s₀ s₉

lemma storage_array_index_access_bytes32_dyn__dyn_5219_abs_of_concrete {s₀ s₉ : State} {slot offset index} :
  Spec (storage_array_index_access_bytes32_dyn__dyn_5219_concrete_of_code.1 slot offset index) s₀ s₉ →
  Spec (A_storage_array_index_access_bytes32_dyn__dyn_5219 slot offset index) s₀ s₉ := by
  intro h
  simpa [A_storage_array_index_access_bytes32_dyn__dyn_5219] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
