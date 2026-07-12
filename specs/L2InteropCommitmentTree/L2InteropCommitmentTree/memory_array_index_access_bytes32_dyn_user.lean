import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2600721580863995212
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.memory_array_index_access_bytes32_dyn_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_memory_array_index_access_bytes32_dyn (addr : Identifier) (baseRef index : Literal) (s₀ s₉ : State) : Prop := memory_array_index_access_bytes32_dyn_concrete_of_code.1 addr baseRef index s₀ s₉

lemma memory_array_index_access_bytes32_dyn_abs_of_concrete {s₀ s₉ : State} {addr baseRef index} :
  Spec (memory_array_index_access_bytes32_dyn_concrete_of_code.1 addr baseRef index) s₀ s₉ →
  Spec (A_memory_array_index_access_bytes32_dyn addr baseRef index) s₀ s₉ := by
  intro h
  simpa [A_memory_array_index_access_bytes32_dyn] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
