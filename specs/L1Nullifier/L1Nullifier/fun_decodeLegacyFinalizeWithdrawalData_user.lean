import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.require_helper_error_L2WithdrawalMessageWrongLength_uint256
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.allocate_memory_array_string
import generated.L1Nullifier.L1Nullifier.abi_encode_bytes
import generated.L1Nullifier.L1Nullifier.fun_encodeBridgeMintData

import generated.L1Nullifier.L1Nullifier.fun_decodeLegacyFinalizeWithdrawalData_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_fun_decodeLegacyFinalizeWithdrawalData (var_functionSignature var_l1Token var_transferData_mpos : Identifier) (var_l1ChainId var__l2ToL1message_mpos : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_decodeLegacyFinalizeWithdrawalData_abs_of_concrete {s₀ s₉ : State} {var_functionSignature var_l1Token var_transferData_mpos var_l1ChainId var__l2ToL1message_mpos} :
  Spec (fun_decodeLegacyFinalizeWithdrawalData_concrete_of_code.1 var_functionSignature var_l1Token var_transferData_mpos var_l1ChainId var__l2ToL1message_mpos) s₀ s₉ →
  Spec (A_fun_decodeLegacyFinalizeWithdrawalData var_functionSignature var_l1Token var_transferData_mpos var_l1ChainId var__l2ToL1message_mpos) s₀ s₉ := by
  unfold A_fun_decodeLegacyFinalizeWithdrawalData
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
