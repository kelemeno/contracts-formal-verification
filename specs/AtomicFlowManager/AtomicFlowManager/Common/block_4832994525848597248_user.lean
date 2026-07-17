import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4832994525848597248_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_4832994525848597248 (s₀ s₉ : State) : Prop := sorry

lemma block_4832994525848597248_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4832994525848597248_concrete_of_code s₀ s₉ →
  Spec A_block_4832994525848597248 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
