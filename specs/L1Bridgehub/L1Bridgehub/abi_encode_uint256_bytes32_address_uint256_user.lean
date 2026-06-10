import Clear.ReasoningPrinciple


import generated.L1Bridgehub.L1Bridgehub.abi_encode_uint256_bytes32_address_uint256_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_uint256_bytes32_address_uint256 (tail : Identifier) (headStart value0 value1 value2 value3 : Literal) (s₀ s₉ : State) : Prop :=
  abi_encode_uint256_bytes32_address_uint256_concrete_of_code.1 tail headStart value0 value1 value2 value3 s₀ s₉

lemma abi_encode_uint256_bytes32_address_uint256_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2 value3} :
  Spec (abi_encode_uint256_bytes32_address_uint256_concrete_of_code.1 tail headStart value0 value1 value2 value3) s₀ s₉ →
  Spec (A_abi_encode_uint256_bytes32_address_uint256 tail headStart value0 value1 value2 value3) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_uint256_bytes32_address_uint256] using h

end

end generated.L1Bridgehub.L1Bridgehub
