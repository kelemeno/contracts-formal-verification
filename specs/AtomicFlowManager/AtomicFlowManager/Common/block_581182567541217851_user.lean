import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_581182567541217851_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_581182567541217851 (s₀ s₉ : State) : Prop := block_581182567541217851_concrete_of_code.1 s₀ s₉

lemma block_581182567541217851_abs_of_concrete {s₀ s₉ : State} :
  Spec block_581182567541217851_concrete_of_code s₀ s₉ →
  Spec A_block_581182567541217851 s₀ s₉ := by
  intro h
  simpa [A_block_581182567541217851] using h

end

end AtomicFlowManager.Common
