import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_6661391401374092343

import generated.L1Nullifier.L1Nullifier.require_helper_error_WithdrawalAlreadyFinalized_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_require_helper_error_WithdrawalAlreadyFinalized  (condition : Literal) (s₀ s₉ : State) : Prop := sorry

lemma require_helper_error_WithdrawalAlreadyFinalized_abs_of_concrete {s₀ s₉ : State} { condition} :
  Spec (require_helper_error_WithdrawalAlreadyFinalized_concrete_of_code.1  condition) s₀ s₉ →
  Spec (A_require_helper_error_WithdrawalAlreadyFinalized  condition) s₀ s₉ := by
  unfold require_helper_error_WithdrawalAlreadyFinalized_concrete_of_code A_require_helper_error_WithdrawalAlreadyFinalized
  sorry

end

end generated.L1Nullifier.L1Nullifier
