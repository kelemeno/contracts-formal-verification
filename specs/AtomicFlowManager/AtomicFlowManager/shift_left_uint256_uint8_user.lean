import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.shift_left_uint256_uint8_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_shift_left_uint256_uint8 (result : Identifier) (value : Literal) (s₀ s₉ : State) : Prop := shift_left_uint256_uint8_concrete_of_code.1 result value s₀ s₉

lemma shift_left_uint256_uint8_abs_of_concrete {s₀ s₉ : State} {result value} :
  Spec (shift_left_uint256_uint8_concrete_of_code.1 result value) s₀ s₉ →
  Spec (A_shift_left_uint256_uint8 result value) s₀ s₉ := by
  intro h
  simpa [A_shift_left_uint256_uint8] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
