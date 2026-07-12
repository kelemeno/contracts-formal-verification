import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_3811156559814846904_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_3811156559814846904 (s₀ s₉ : State) : Prop := sorry

lemma block_3811156559814846904_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3811156559814846904_concrete_of_code s₀ s₉ →
  Spec A_block_3811156559814846904 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
