import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.fun_requireNotPaused
import generated.L1Nullifier.L1Nullifier.cleanup_uint16
import generated.L1Nullifier.L1Nullifier.validator_assert_enum_TxStatus
import generated.L1Nullifier.L1Nullifier.Common.if_6204704137440835262
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_bool_fromMemory
import generated.L1Nullifier.L1Nullifier.require_helper_error_InvalidProof
import generated.L1Nullifier.L1Nullifier.fun_getLeafHashFromLog
import generated.L1Nullifier.L1Nullifier.fun_getL2LogFromL1ToL2Transaction
import generated.L1Nullifier.L1Nullifier.Common.if_2160268309564231326
import generated.L1Nullifier.L1Nullifier.abi_decode_struct_ProofData_fromMemory
import generated.L1Nullifier.L1Nullifier.checked_add_uint256
import generated.L1Nullifier.L1Nullifier.fun_isPreSharedBridgeDepositOnEra
import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17729
import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.cleanup_bool
import generated.L1Nullifier.L1Nullifier.fun_encodeTxDataHash

import generated.L1Nullifier.L1Nullifier.modifier_whenNotPaused_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_modifier_whenNotPaused  (var__confirmTransferResultData_mpos : Literal) (s₀ s₉ : State) : Prop := True

lemma modifier_whenNotPaused_abs_of_concrete {s₀ s₉ : State} { var__confirmTransferResultData_mpos} :
  Spec (modifier_whenNotPaused_concrete_of_code.1 var__confirmTransferResultData_mpos) s₀ s₉ →
  Spec (A_modifier_whenNotPaused var__confirmTransferResultData_mpos) s₀ s₉ := by
  unfold A_modifier_whenNotPaused
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
