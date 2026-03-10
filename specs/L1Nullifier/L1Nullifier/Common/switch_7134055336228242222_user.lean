import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.switch_3928722633135334235
import generated.L1Nullifier.L1Nullifier.fun_decodeAssetRouterFinalizeDepositData
import generated.L1Nullifier.L1Nullifier.fun_decodeLegacyFinalizeWithdrawalData
import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_uint256_fromMemory
import generated.L1Nullifier.L1Nullifier.require_helper_error_TokenNotLegacy
import generated.L1Nullifier.L1Nullifier.fun_decodeBaseTokenFinalizeWithdrawalData
import generated.L1Nullifier.L1Nullifier.Common.if_6864078037843212115
import generated.L1Nullifier.L1Nullifier.Common.if_3075873538421022416
import generated.L1Nullifier.L1Nullifier.fun_encodeBridgeMintData_17779
import generated.L1Nullifier.L1Nullifier.allocate_and_zero_memory_array_bytes

import generated.L1Nullifier.L1Nullifier.Common.switch_7134055336228242222_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_switch_7134055336228242222 (s₀ s₉ : State) : Prop := True

lemma switch_7134055336228242222_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_7134055336228242222_concrete_of_code s₀ s₉ →
  Spec A_switch_7134055336228242222 s₀ s₉ := by
  unfold A_switch_7134055336228242222
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common
