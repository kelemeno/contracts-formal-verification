import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2046548234894414874_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_2046548234894414874 (s₀ s₉ : State) : Prop := block_2046548234894414874_concrete_of_code.1 s₀ s₉

lemma block_2046548234894414874_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2046548234894414874_concrete_of_code s₀ s₉ →
  Spec A_block_2046548234894414874 s₀ s₉ := by
  intro h
  simpa [A_block_2046548234894414874] using h

end

end AtomicFlowManager.Common
