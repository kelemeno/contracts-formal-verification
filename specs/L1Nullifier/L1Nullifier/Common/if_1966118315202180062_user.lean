import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.panic_error_0x41

import generated.L1Nullifier.L1Nullifier.Common.if_1966118315202180062_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_1966118315202180062 (s₀ s₉ : State) : Prop :=
  if_1966118315202180062_concrete_of_code.1 s₀ s₉

lemma if_1966118315202180062_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1966118315202180062_concrete_of_code s₀ s₉ →
  Spec A_if_1966118315202180062 s₀ s₉ := by
  intro h
  simpa [A_if_1966118315202180062] using h

end

end L1Nullifier.Common
