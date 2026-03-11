import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.fun_requireNotPaused
import generated.L1Nullifier.L1Nullifier.require_helper_error_WithdrawalAlreadyFinalized
import generated.L1Nullifier.L1Nullifier.cleanup_bool
import generated.L1Nullifier.L1Nullifier.update_storage_value_offset_bool_to_bool_17751
import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256
import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17749
import generated.L1Nullifier.L1Nullifier.fun_verifyWithdrawal
import generated.L1Nullifier.L1Nullifier.fun_isPreSharedBridgeEraEthWithdrawal
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_bool_fromMemory
import generated.L1Nullifier.L1Nullifier.fun_isPreSharedBridgeEraTokenWithdrawal
import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.Common.if_396429549932726667
import generated.L1Nullifier.L1Nullifier.Common.if_3525216432756457624
import generated.L1Nullifier.L1Nullifier.abi_decode

import generated.L1Nullifier.L1Nullifier.modifier_nonReentrant_892_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_modifier_nonReentrant_892  (var_finalizeWithdrawalParams_889_mpos : Literal) (s₀ s₉ : State) : Prop := True

lemma modifier_nonReentrant_892_abs_of_concrete {s₀ s₉ : State} { var_finalizeWithdrawalParams_889_mpos} :
  Spec (modifier_nonReentrant_892_concrete_of_code.1 var_finalizeWithdrawalParams_889_mpos) s₀ s₉ →
  Spec (A_modifier_nonReentrant_892 var_finalizeWithdrawalParams_889_mpos) s₀ s₉ := by
  unfold A_modifier_nonReentrant_892
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
