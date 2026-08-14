import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_618803822011296348_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_618803822011296348 (s₀ s₉ : State) : Prop :=
  block_618803822011296348_concrete_of_code.1 s₀ s₉
lemma block_618803822011296348_abs_of_concrete {s₀ s₉ : State} :
  Spec block_618803822011296348_concrete_of_code s₀ s₉ →
  Spec A_block_618803822011296348 s₀ s₉ := by
  intro h
  simpa [A_block_618803822011296348] using h

end

end InteropHandler.Common
