import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.block_5755787097143698222_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_5755787097143698222 (s₀ s₉ : State) : Prop := block_5755787097143698222_concrete_of_code.1 s₀ s₉

lemma block_5755787097143698222_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5755787097143698222_concrete_of_code s₀ s₉ →
  Spec A_block_5755787097143698222 s₀ s₉ := by
  intro h
  simpa [A_block_5755787097143698222] using h

end

end L2InteropHandler.Common
