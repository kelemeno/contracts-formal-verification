import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_7619396719100115431_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_7619396719100115431 (s₀ s₉ : State) : Prop := sorry

lemma block_7619396719100115431_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7619396719100115431_concrete_of_code s₀ s₉ →
  Spec A_block_7619396719100115431 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
