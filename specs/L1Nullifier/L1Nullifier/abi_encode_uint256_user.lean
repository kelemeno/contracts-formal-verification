import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.abi_encode_uint256_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_uint256 (tail : Identifier) (headStart value0 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_uint256_abs_of_concrete {s₀ s₉ : State} {tail headStart value0} :
  Spec (abi_encode_uint256_concrete_of_code.1 tail headStart value0) s₀ s₉ →
  Spec (A_abi_encode_uint256 tail headStart value0) s₀ s₉ := by
  unfold abi_encode_uint256_concrete_of_code A_abi_encode_uint256
  sorry

end

end generated.L1Nullifier.L1Nullifier
