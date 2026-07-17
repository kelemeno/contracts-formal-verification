import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_uint256_7838_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_uint256_uint256_7838 (tail : Identifier) (value0 value1 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_uint256_uint256_7838_abs_of_concrete {s₀ s₉ : State} {tail value0 value1} :
  Spec (abi_encode_uint256_uint256_7838_concrete_of_code.1 tail value0 value1) s₀ s₉ →
  Spec (A_abi_encode_uint256_uint256_7838 tail value0 value1) s₀ s₉ := by
  unfold abi_encode_uint256_uint256_7838_concrete_of_code A_abi_encode_uint256_uint256_7838
  sorry

end

end generated.AtomicFlowManager.AtomicFlowManager
