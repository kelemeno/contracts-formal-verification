import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_3995168818704772226

import generated.L2InteropHandler.L2InteropHandler.array_allocation_size_array_bytes32_dyn_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_array_allocation_size_array_bytes32_dyn (size : Identifier) (length : Literal) (s₀ s₉ : State) : Prop := sorry

lemma array_allocation_size_array_bytes32_dyn_abs_of_concrete {s₀ s₉ : State} {size length} :
  Spec (array_allocation_size_array_bytes32_dyn_concrete_of_code.1 size length) s₀ s₉ →
  Spec (A_array_allocation_size_array_bytes32_dyn size length) s₀ s₉ := by
  unfold array_allocation_size_array_bytes32_dyn_concrete_of_code A_array_allocation_size_array_bytes32_dyn
  sorry

end

end generated.L2InteropHandler.L2InteropHandler
