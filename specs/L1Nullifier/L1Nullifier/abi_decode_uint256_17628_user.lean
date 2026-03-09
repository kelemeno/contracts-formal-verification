import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.abi_decode_uint256_17628_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_decode_uint256_17628 (value : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_uint256_17628_abs_of_concrete {s₀ s₉ : State} {value } :
  Spec (abi_decode_uint256_17628_concrete_of_code.1 value ) s₀ s₉ →
  Spec (A_abi_decode_uint256_17628 value ) s₀ s₉ := by
  unfold abi_decode_uint256_17628_concrete_of_code A_abi_decode_uint256_17628
  sorry

end

end generated.L1Nullifier.L1Nullifier
