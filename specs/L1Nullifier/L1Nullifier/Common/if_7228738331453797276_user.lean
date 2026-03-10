import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_uint256_uint256
import generated.L1Nullifier.L1Nullifier.Common.if_4378373803491156100
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.Common.if_776970635549065007
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_bool_fromMemory
import generated.L1Nullifier.L1Nullifier.require_helper_error_WithdrawalAlreadyFinalized
import generated.L1Nullifier.L1Nullifier.fun_isPreSharedBridgeEraEthWithdrawal

import generated.L1Nullifier.L1Nullifier.Common.if_7228738331453797276_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_7228738331453797276 (s₀ s₉ : State) : Prop := True

lemma if_7228738331453797276_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7228738331453797276_concrete_of_code s₀ s₉ →
  Spec A_if_7228738331453797276 s₀ s₉ := by
  unfold A_if_7228738331453797276
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common
