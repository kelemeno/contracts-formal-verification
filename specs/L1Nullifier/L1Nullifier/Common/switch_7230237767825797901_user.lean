import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.switch_1699289825284573029
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.bytes_concat_bytes1_bytes
import generated.L1Nullifier.L1Nullifier.Common.if_9097063384830582942
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.Common.if_8366118562963474184
import generated.L1Nullifier.L1Nullifier.abi_decode_address_fromMemory
import generated.L1Nullifier.L1Nullifier.Common.if_4014157399345581313
import generated.L1Nullifier.L1Nullifier.fun_decodeBridgeBurnData

import generated.L1Nullifier.L1Nullifier.Common.switch_7230237767825797901_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_switch_7230237767825797901 (s₀ s₉ : State) : Prop := sorry

lemma switch_7230237767825797901_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_7230237767825797901_concrete_of_code s₀ s₉ →
  Spec A_switch_7230237767825797901 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common
