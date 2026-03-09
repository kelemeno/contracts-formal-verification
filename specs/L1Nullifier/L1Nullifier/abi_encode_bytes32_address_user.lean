import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.abi_encode_bytes32_address_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_bytes32_address (tail : Identifier) (value0 value1 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_bytes32_address_abs_of_concrete {s₀ s₉ : State} {tail value0 value1} :
  Spec (abi_encode_bytes32_address_concrete_of_code.1 tail value0 value1) s₀ s₉ →
  Spec (A_abi_encode_bytes32_address tail value0 value1) s₀ s₉ := by
  unfold abi_encode_bytes32_address_concrete_of_code A_abi_encode_bytes32_address
  sorry

end

end generated.L1Nullifier.L1Nullifier
