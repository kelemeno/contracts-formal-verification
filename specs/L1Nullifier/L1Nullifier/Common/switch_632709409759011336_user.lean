import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.switch_3148763678931997026
import generated.L1Nullifier.L1Nullifier.abi_encode_bytes
import generated.L1Nullifier.L1Nullifier.Common.if_2522888386092718679

import generated.L1Nullifier.L1Nullifier.Common.switch_632709409759011336_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_switch_632709409759011336 (s₀ s₉ : State) : Prop := switch_632709409759011336_concrete_of_code.1 s₀ s₉

lemma switch_632709409759011336_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_632709409759011336_concrete_of_code s₀ s₉ →
  Spec A_switch_632709409759011336 s₀ s₉ := by
  intro h
  simpa [A_switch_632709409759011336] using h

end

end L1Nullifier.Common
