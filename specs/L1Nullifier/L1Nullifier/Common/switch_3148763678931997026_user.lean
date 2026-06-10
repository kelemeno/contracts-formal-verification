import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.block_8391706194969141390
import generated.L1Nullifier.L1Nullifier.Common.block_8507783491343898777
import generated.L1Nullifier.L1Nullifier.abi_encode_bytes

import generated.L1Nullifier.L1Nullifier.Common.switch_3148763678931997026_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_switch_3148763678931997026 (s₀ s₉ : State) : Prop := switch_3148763678931997026_concrete_of_code.1 s₀ s₉

lemma switch_3148763678931997026_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_3148763678931997026_concrete_of_code s₀ s₉ →
  Spec A_switch_3148763678931997026 s₀ s₉ := by
  intro h
  simpa [A_switch_3148763678931997026] using h

end

end L1Nullifier.Common
