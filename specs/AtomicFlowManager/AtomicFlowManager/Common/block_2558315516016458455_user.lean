import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2558315516016458455_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_2558315516016458455 (s₀ s₉ : State) : Prop := sorry

lemma block_2558315516016458455_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2558315516016458455_concrete_of_code s₀ s₉ →
  Spec A_block_2558315516016458455 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
