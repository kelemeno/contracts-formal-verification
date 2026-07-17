import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_bool_uint256_uint64_7917_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_bool_uint256_uint64_7917 (tail : Identifier) (value1 value2 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_bool_uint256_uint64_7917_abs_of_concrete {s₀ s₉ : State} {tail value1 value2} :
  Spec (abi_encode_bool_uint256_uint64_7917_concrete_of_code.1 tail value1 value2) s₀ s₉ →
  Spec (A_abi_encode_bool_uint256_uint64_7917 tail value1 value2) s₀ s₉ := by
  unfold abi_encode_bool_uint256_uint64_7917_concrete_of_code A_abi_encode_bool_uint256_uint64_7917
  sorry

end

end generated.AtomicFlowManager.AtomicFlowManager
