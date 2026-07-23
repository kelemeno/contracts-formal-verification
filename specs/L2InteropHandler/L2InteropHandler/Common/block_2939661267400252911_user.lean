import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.block_2939661267400252911_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_2939661267400252911 (s₀ s₉ : State) : Prop := block_2939661267400252911_concrete_of_code.1 s₀ s₉

lemma block_2939661267400252911_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2939661267400252911_concrete_of_code s₀ s₉ →
  Spec A_block_2939661267400252911 s₀ s₉ := by
  intro h
  simpa [A_block_2939661267400252911] using h

end

end L2InteropHandler.Common
