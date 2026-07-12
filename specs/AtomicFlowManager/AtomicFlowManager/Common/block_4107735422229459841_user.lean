import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4107735422229459841_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_4107735422229459841 (s₀ s₉ : State) : Prop := block_4107735422229459841_concrete_of_code.1 s₀ s₉

lemma block_4107735422229459841_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4107735422229459841_concrete_of_code s₀ s₉ →
  Spec A_block_4107735422229459841 s₀ s₉ := by
  intro h
  simpa [A_block_4107735422229459841] using h

end

end AtomicFlowManager.Common
