import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.block_7103722051132062704
import generated.L1Nullifier.L1Nullifier.Common.block_1256850120741417251
import generated.L1Nullifier.L1Nullifier.abi_encode_uint256_uint256
import generated.L1Nullifier.L1Nullifier.Common.block_5536870490314980881
import generated.L1Nullifier.L1Nullifier.Common.if_4378373803491156100
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.Common.if_3030400364618924393
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_bool_fromMemory
import generated.L1Nullifier.L1Nullifier.require_helper_error_WithdrawalAlreadyFinalized
import generated.L1Nullifier.L1Nullifier.fun_isPreSharedBridgeEraEthWithdrawal

import generated.L1Nullifier.L1Nullifier.Common.if_7574793255574635930_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_7574793255574635930 (s₀ s₉ : State) : Prop := if_7574793255574635930_concrete_of_code.1 s₀ s₉

lemma if_7574793255574635930_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7574793255574635930_concrete_of_code s₀ s₉ →
  Spec A_if_7574793255574635930 s₀ s₉ := by
  intro h
  simpa [A_if_7574793255574635930] using h

end

end L1Nullifier.Common
