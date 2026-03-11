import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.require_helper_error_InvalidProof_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_require_helper_error_InvalidProof  (condition : Literal) (s₀ s₉ : State) : Prop :=
  require_helper_error_InvalidProof_concrete_of_code.1 condition s₀ s₉

lemma require_helper_error_InvalidProof_abs_of_concrete {s₀ s₉ : State} { condition} :
  Spec (require_helper_error_InvalidProof_concrete_of_code.1 condition) s₀ s₉ →
  Spec (A_require_helper_error_InvalidProof condition) s₀ s₉ := by
  intro h
  simpa [A_require_helper_error_InvalidProof] using h

end

end generated.L1Nullifier.L1Nullifier
