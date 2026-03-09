import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.constant_L2_ASSET_ROUTER_ADDR
import generated.L1Nullifier.L1Nullifier.Common.if_1772412277184739373
import generated.L1Nullifier.L1Nullifier.require_helper_error_WrongL2Sender_address

import generated.L1Nullifier.L1Nullifier.Common.switch_2083441642682059880_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_switch_2083441642682059880 (s₀ s₉ : State) : Prop := sorry

lemma switch_2083441642682059880_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_2083441642682059880_concrete_of_code s₀ s₉ →
  Spec A_switch_2083441642682059880 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common
