import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.abi_decode_uint256_17652_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_decode_uint256_17652 (value : Identifier)  (s₀ s₉ : State) : Prop := abi_decode_uint256_17652_concrete_of_code.1 value s₀ s₉

lemma abi_decode_uint256_17652_abs_of_concrete {s₀ s₉ : State} {value } :
  Spec (abi_decode_uint256_17652_concrete_of_code.1 value ) s₀ s₉ →
  Spec (A_abi_decode_uint256_17652 value ) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_uint256_17652] using h

end

end generated.L1Nullifier.L1Nullifier
