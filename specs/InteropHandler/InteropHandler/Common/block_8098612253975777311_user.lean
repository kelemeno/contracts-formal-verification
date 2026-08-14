import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_8098612253975777311_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_8098612253975777311 (s₀ s₉ : State) : Prop :=
  block_8098612253975777311_concrete_of_code.1 s₀ s₉
lemma block_8098612253975777311_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8098612253975777311_concrete_of_code s₀ s₉ →
  Spec A_block_8098612253975777311 s₀ s₉ := by
  intro h
  simpa [A_block_8098612253975777311] using h

end

end InteropHandler.Common
