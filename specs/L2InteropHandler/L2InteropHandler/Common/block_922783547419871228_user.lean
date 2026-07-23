import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.block_922783547419871228_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_922783547419871228 (s₀ s₉ : State) : Prop := block_922783547419871228_concrete_of_code.1 s₀ s₉

lemma block_922783547419871228_abs_of_concrete {s₀ s₉ : State} :
  Spec block_922783547419871228_concrete_of_code s₀ s₉ →
  Spec A_block_922783547419871228 s₀ s₉ := by
  intro h
  simpa [A_block_922783547419871228] using h

end

end L2InteropHandler.Common
