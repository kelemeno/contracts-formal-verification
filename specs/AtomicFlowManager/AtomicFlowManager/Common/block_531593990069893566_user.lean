import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_531593990069893566_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_531593990069893566 (s₀ s₉ : State) : Prop := sorry

lemma block_531593990069893566_abs_of_concrete {s₀ s₉ : State} :
  Spec block_531593990069893566_concrete_of_code s₀ s₉ →
  Spec A_block_531593990069893566 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
