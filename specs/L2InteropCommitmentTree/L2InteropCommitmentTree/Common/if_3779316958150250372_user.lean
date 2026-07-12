import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_4496777052991139710

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_3779316958150250372_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common 

def A_if_3779316958150250372 (s₀ s₉ : State) : Prop := if_3779316958150250372_concrete_of_code.1 s₀ s₉

lemma if_3779316958150250372_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3779316958150250372_concrete_of_code s₀ s₉ →
  Spec A_if_3779316958150250372 s₀ s₉ := by
  intro h
  simpa [A_if_3779316958150250372] using h

end

end L2InteropCommitmentTree.Common
