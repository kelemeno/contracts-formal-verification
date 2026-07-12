import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1916803620570040585_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_1916803620570040585 (s₀ s₉ : State) : Prop := block_1916803620570040585_concrete_of_code.1 s₀ s₉

lemma block_1916803620570040585_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1916803620570040585_concrete_of_code s₀ s₉ →
  Spec A_block_1916803620570040585 s₀ s₉ := by
  intro h
  simpa [A_block_1916803620570040585] using h

end

end L2InteropCommitmentTree.Common
