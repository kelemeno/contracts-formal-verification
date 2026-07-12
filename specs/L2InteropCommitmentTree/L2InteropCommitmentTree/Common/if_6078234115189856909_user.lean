import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_6078234115189856909_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_6078234115189856909 (s₀ s₉ : State) : Prop := if_6078234115189856909_concrete_of_code.1 s₀ s₉

lemma if_6078234115189856909_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6078234115189856909_concrete_of_code s₀ s₉ →
  Spec A_if_6078234115189856909 s₀ s₉ := by
  intro h
  simpa [A_if_6078234115189856909] using h

end

end L2InteropCommitmentTree.Common
