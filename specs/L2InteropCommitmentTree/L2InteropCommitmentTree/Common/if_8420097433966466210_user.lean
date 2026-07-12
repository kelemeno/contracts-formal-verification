import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_8420097433966466210_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_if_8420097433966466210 (s₀ s₉ : State) : Prop := if_8420097433966466210_concrete_of_code.1 s₀ s₉

lemma if_8420097433966466210_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8420097433966466210_concrete_of_code s₀ s₉ →
  Spec A_if_8420097433966466210 s₀ s₉ := by
  intro h
  simpa [A_if_8420097433966466210] using h

end

end L2InteropCommitmentTree.Common
