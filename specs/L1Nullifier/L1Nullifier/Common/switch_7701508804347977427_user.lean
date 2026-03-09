import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_address_bytes32_bytes
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.bytes_concat_bytes1_bytes

import generated.L1Nullifier.L1Nullifier.Common.switch_7701508804347977427_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_switch_7701508804347977427 (s₀ s₉ : State) : Prop := sorry

lemma switch_7701508804347977427_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_7701508804347977427_concrete_of_code s₀ s₉ →
  Spec A_switch_7701508804347977427 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common
