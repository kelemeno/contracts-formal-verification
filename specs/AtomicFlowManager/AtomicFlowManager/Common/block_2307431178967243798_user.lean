import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2307431178967243798_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_2307431178967243798 (s₀ s₉ : State) : Prop := block_2307431178967243798_concrete_of_code.1 s₀ s₉

lemma block_2307431178967243798_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2307431178967243798_concrete_of_code s₀ s₉ →
  Spec A_block_2307431178967243798 s₀ s₉ := by
  intro h
  simpa [A_block_2307431178967243798] using h

end

end AtomicFlowManager.Common
