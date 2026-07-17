import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4222795547505584607_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_4222795547505584607 (s₀ s₉ : State) : Prop := sorry

lemma block_4222795547505584607_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4222795547505584607_concrete_of_code s₀ s₉ →
  Spec A_block_4222795547505584607 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
