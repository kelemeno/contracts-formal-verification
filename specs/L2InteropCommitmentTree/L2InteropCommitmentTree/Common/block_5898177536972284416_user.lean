import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_5898177536972284416_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_5898177536972284416 (s₀ s₉ : State) : Prop := block_5898177536972284416_concrete_of_code.1 s₀ s₉

lemma block_5898177536972284416_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5898177536972284416_concrete_of_code s₀ s₉ →
  Spec A_block_5898177536972284416 s₀ s₉ := by
  intro h
  simpa [A_block_5898177536972284416] using h

end

end L2InteropCommitmentTree.Common
