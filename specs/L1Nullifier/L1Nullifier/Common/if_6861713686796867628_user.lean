import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.panic_error_0x41

import generated.L1Nullifier.L1Nullifier.Common.if_6861713686796867628_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_6861713686796867628 (s₀ s₉ : State) : Prop :=
  if_6861713686796867628_concrete_of_code.1 s₀ s₉

lemma if_6861713686796867628_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6861713686796867628_concrete_of_code s₀ s₉ →
  Spec A_if_6861713686796867628 s₀ s₉ := by
  intro h
  simpa [A_if_6861713686796867628] using h

end

end L1Nullifier.Common
