import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_uint256_7410_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_decode_uint256_7410 (value : Identifier)  (s₀ s₉ : State) : Prop := abi_decode_uint256_7410_concrete_of_code.1 value s₀ s₉

lemma abi_decode_uint256_7410_abs_of_concrete {s₀ s₉ : State} {value } :
  Spec (abi_decode_uint256_7410_concrete_of_code.1 value ) s₀ s₉ →
  Spec (A_abi_decode_uint256_7410 value ) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_uint256_7410] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
