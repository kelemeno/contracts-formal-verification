import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_5792510925045852942_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_if_5792510925045852942 (s₀ s₉ : State) : Prop := if_5792510925045852942_concrete_of_code.1 s₀ s₉

lemma if_5792510925045852942_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5792510925045852942_concrete_of_code s₀ s₉ →
  Spec A_if_5792510925045852942 s₀ s₉ := by
  intro h
  simpa [A_if_5792510925045852942] using h

end

end L2InteropCommitmentTree.Common
