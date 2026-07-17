import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bytes32_7837_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_decode_bytes32_7837 (value : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_bytes32_7837_abs_of_concrete {s₀ s₉ : State} {value } :
  Spec (abi_decode_bytes32_7837_concrete_of_code.1 value ) s₀ s₉ →
  Spec (A_abi_decode_bytes32_7837 value ) s₀ s₉ := by
  unfold abi_decode_bytes32_7837_concrete_of_code A_abi_decode_bytes32_7837
  sorry

end

end generated.AtomicFlowManager.AtomicFlowManager
