import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3897550251423386602_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_3897550251423386602 (s₀ s₉ : State) : Prop := block_3897550251423386602_concrete_of_code.1 s₀ s₉

lemma block_3897550251423386602_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3897550251423386602_concrete_of_code s₀ s₉ →
  Spec A_block_3897550251423386602 s₀ s₉ := by
  intro h
  simpa [A_block_3897550251423386602] using h

end

end AtomicFlowManager.Common
