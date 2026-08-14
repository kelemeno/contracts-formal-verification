import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_6897250089820179679_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_6897250089820179679 (s₀ s₉ : State) : Prop :=
  block_6897250089820179679_concrete_of_code.1 s₀ s₉
lemma block_6897250089820179679_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6897250089820179679_concrete_of_code s₀ s₉ →
  Spec A_block_6897250089820179679 s₀ s₉ := by
  intro h
  simpa [A_block_6897250089820179679] using h

end

end InteropHandler.Common
