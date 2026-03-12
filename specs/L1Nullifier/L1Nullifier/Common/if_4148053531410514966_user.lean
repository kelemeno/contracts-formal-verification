import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.panic_error_0x41

import generated.L1Nullifier.L1Nullifier.Common.if_4148053531410514966_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_4148053531410514966 (s₀ s₉ : State) : Prop :=
  if_4148053531410514966_concrete_of_code.1 s₀ s₉

lemma if_4148053531410514966_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4148053531410514966_concrete_of_code s₀ s₉ →
  Spec A_if_4148053531410514966 s₀ s₉ := by
  intro h
  simpa [A_if_4148053531410514966] using h

end

end L1Nullifier.Common
