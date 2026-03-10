import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.abi_encode_uint256_uint256
import generated.L1Nullifier.L1Nullifier.Common.if_1475492890989233506
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.Common.if_7909756524521358901
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_bool_fromMemory
import generated.L1Nullifier.L1Nullifier.require_helper_error_WithdrawalAlreadyFinalized
import generated.L1Nullifier.L1Nullifier.fun_isPreSharedBridgeEraTokenWithdrawal

import generated.L1Nullifier.L1Nullifier.Common.if_8885061995403076879_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_8885061995403076879 (s₀ s₉ : State) : Prop := sorry

lemma if_8885061995403076879_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8885061995403076879_concrete_of_code s₀ s₉ →
  Spec A_if_8885061995403076879 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common
