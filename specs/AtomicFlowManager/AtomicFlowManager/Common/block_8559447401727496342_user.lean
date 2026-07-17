import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8559447401727496342_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_8559447401727496342 (s₀ s₉ : State) : Prop := sorry

lemma block_8559447401727496342_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8559447401727496342_concrete_of_code s₀ s₉ →
  Spec A_block_8559447401727496342 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
