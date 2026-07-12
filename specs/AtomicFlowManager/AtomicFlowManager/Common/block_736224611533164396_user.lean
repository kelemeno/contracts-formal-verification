import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_736224611533164396_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_736224611533164396 (s₀ s₉ : State) : Prop := block_736224611533164396_concrete_of_code.1 s₀ s₉

lemma block_736224611533164396_abs_of_concrete {s₀ s₉ : State} :
  Spec block_736224611533164396_concrete_of_code s₀ s₉ →
  Spec A_block_736224611533164396 s₀ s₉ := by
  intro h
  simpa [A_block_736224611533164396] using h

end

end AtomicFlowManager.Common
