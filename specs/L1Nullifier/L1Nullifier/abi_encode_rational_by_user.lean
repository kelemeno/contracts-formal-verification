import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.abi_encode_rational_by_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_rational_by (tail : Identifier) (headStart : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_rational_by_abs_of_concrete {s₀ s₉ : State} {tail headStart} :
  Spec (abi_encode_rational_by_concrete_of_code.1 tail headStart) s₀ s₉ →
  Spec (A_abi_encode_rational_by tail headStart) s₀ s₉ := by
  unfold abi_encode_rational_by_concrete_of_code A_abi_encode_rational_by
  sorry

end

end generated.L1Nullifier.L1Nullifier
