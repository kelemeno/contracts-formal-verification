import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.require_helper_error_L2WithdrawalMessageWrongLength_uint256

import generated.L1Nullifier.L1Nullifier.fun_decodeBaseTokenFinalizeWithdrawalData_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_fun_decodeBaseTokenFinalizeWithdrawalData (var_functionSignature var_l1Receiver var_amount : Identifier) (var_l2ToL1message_5663_mpos : Literal) (s₀ s₉ : State) : Prop :=
  fun_decodeBaseTokenFinalizeWithdrawalData_concrete_of_code.1 var_functionSignature var_l1Receiver var_amount var_l2ToL1message_5663_mpos s₀ s₉

lemma fun_decodeBaseTokenFinalizeWithdrawalData_abs_of_concrete {s₀ s₉ : State} {var_functionSignature var_l1Receiver var_amount var_l2ToL1message_5663_mpos} :
  Spec (fun_decodeBaseTokenFinalizeWithdrawalData_concrete_of_code.1 var_functionSignature var_l1Receiver var_amount var_l2ToL1message_5663_mpos) s₀ s₉ →
  Spec (A_fun_decodeBaseTokenFinalizeWithdrawalData var_functionSignature var_l1Receiver var_amount var_l2ToL1message_5663_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_decodeBaseTokenFinalizeWithdrawalData] using h

end

end generated.L1Nullifier.L1Nullifier
