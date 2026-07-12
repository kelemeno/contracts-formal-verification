import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4006823798342809328_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_4006823798342809328 (s₀ s₉ : State) : Prop := if_4006823798342809328_concrete_of_code.1 s₀ s₉

lemma if_4006823798342809328_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4006823798342809328_concrete_of_code s₀ s₉ →
  Spec A_if_4006823798342809328 s₀ s₉ := by
  intro h
  simpa [A_if_4006823798342809328] using h

end

end L2InteropCommitmentTree.Common
