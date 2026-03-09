import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.cleanup_uint16_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_cleanup_uint16 (cleaned : Identifier) (value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma cleanup_uint16_abs_of_concrete {s₀ s₉ : State} {cleaned value} :
  Spec (cleanup_uint16_concrete_of_code.1 cleaned value) s₀ s₉ →
  Spec (A_cleanup_uint16 cleaned value) s₀ s₉ := by
  unfold cleanup_uint16_concrete_of_code A_cleanup_uint16
  sorry

end

end generated.L1Nullifier.L1Nullifier
