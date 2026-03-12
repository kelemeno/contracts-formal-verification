import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.require_helper_error_ZeroAddress_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_require_helper_error_ZeroAddress  (condition : Literal) (s₀ s₉ : State) : Prop :=
  require_helper_error_ZeroAddress_concrete_of_code.1 condition s₀ s₉

lemma require_helper_error_ZeroAddress_abs_of_concrete {s₀ s₉ : State} { condition} :
  Spec (require_helper_error_ZeroAddress_concrete_of_code.1 condition) s₀ s₉ →
  Spec (A_require_helper_error_ZeroAddress condition) s₀ s₉ := by
  intro h
  simpa [A_require_helper_error_ZeroAddress] using h

end

end generated.L1Nullifier.L1Nullifier
