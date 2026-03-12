import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.panic_error_0x11

import generated.L1Nullifier.L1Nullifier.Common.if_2095837721993293218_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_2095837721993293218 (s₀ s₉ : State) : Prop :=
  if_2095837721993293218_concrete_of_code.1 s₀ s₉

lemma if_2095837721993293218_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2095837721993293218_concrete_of_code s₀ s₉ →
  Spec A_if_2095837721993293218 s₀ s₉ := by
  intro h
  simpa [A_if_2095837721993293218] using h

end

end L1Nullifier.Common
