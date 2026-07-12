import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4148053531410514966
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_allocation_size_array_bytes32_dyn_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_array_allocation_size_array_bytes32_dyn (size : Identifier) (length : Literal) (s₀ s₉ : State) : Prop := array_allocation_size_array_bytes32_dyn_concrete_of_code.1 size length s₀ s₉

lemma array_allocation_size_array_bytes32_dyn_abs_of_concrete {s₀ s₉ : State} {size length} :
  Spec (array_allocation_size_array_bytes32_dyn_concrete_of_code.1 size length) s₀ s₉ →
  Spec (A_array_allocation_size_array_bytes32_dyn size length) s₀ s₉ := by
  intro h
  simpa [A_array_allocation_size_array_bytes32_dyn] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
