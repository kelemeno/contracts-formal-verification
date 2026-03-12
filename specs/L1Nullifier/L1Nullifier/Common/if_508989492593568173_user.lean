import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode

import generated.L1Nullifier.L1Nullifier.Common.if_508989492593568173_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_508989492593568173 (s₀ s₉ : State) : Prop :=
  if_508989492593568173_concrete_of_code.1 s₀ s₉

lemma if_508989492593568173_abs_of_concrete {s₀ s₉ : State} :
  Spec if_508989492593568173_concrete_of_code s₀ s₉ →
  Spec A_if_508989492593568173 s₀ s₉ := by
  intro h
  simpa [A_if_508989492593568173] using h

end

end L1Nullifier.Common
