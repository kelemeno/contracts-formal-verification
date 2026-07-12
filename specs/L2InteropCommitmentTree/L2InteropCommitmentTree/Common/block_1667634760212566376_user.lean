import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1667634760212566376_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_1667634760212566376 (s₀ s₉ : State) : Prop := block_1667634760212566376_concrete_of_code.1 s₀ s₉

lemma block_1667634760212566376_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1667634760212566376_concrete_of_code s₀ s₉ →
  Spec A_block_1667634760212566376 s₀ s₉ := by
  intro h
  simpa [A_block_1667634760212566376] using h

end

end L2InteropCommitmentTree.Common
