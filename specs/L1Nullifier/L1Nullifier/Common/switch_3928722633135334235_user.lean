import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.switch_5095553012142514140
import generated.L1Nullifier.L1Nullifier.fun_decodeAssetRouterFinalizeDepositData
import generated.L1Nullifier.L1Nullifier.fun_decodeLegacyFinalizeWithdrawalData
import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.Common.if_7069222774777857031
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.Common.if_4354079312647531195
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_uint256_fromMemory
import generated.L1Nullifier.L1Nullifier.require_helper_error_TokenNotLegacy

import generated.L1Nullifier.L1Nullifier.Common.switch_3928722633135334235_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_switch_3928722633135334235 (s₀ s₉ : State) : Prop := True

lemma switch_3928722633135334235_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_3928722633135334235_concrete_of_code s₀ s₉ →
  Spec A_switch_3928722633135334235 s₀ s₉ := by
  unfold A_switch_3928722633135334235
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common
