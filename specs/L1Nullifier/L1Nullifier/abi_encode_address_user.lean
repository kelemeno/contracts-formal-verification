import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.abi_encode_address_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_address (tail : Identifier) (headStart value0 : Literal) (s₀ s₉ : State) : Prop := abi_encode_address_concrete_of_code.1 tail headStart value0 s₀ s₉

lemma abi_encode_address_abs_of_concrete {s₀ s₉ : State} {tail headStart value0} :
  Spec (abi_encode_address_concrete_of_code.1 tail headStart value0) s₀ s₉ →
  Spec (A_abi_encode_address tail headStart value0) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_address] using h

end

end generated.L1Nullifier.L1Nullifier
