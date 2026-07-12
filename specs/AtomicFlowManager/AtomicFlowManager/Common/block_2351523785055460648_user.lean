import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2351523785055460648_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_2351523785055460648 (s₀ s₉ : State) : Prop := block_2351523785055460648_concrete_of_code.1 s₀ s₉

lemma block_2351523785055460648_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2351523785055460648_concrete_of_code s₀ s₉ →
  Spec A_block_2351523785055460648 s₀ s₉ := by
  intro h
  simpa [A_block_2351523785055460648] using h

end

end AtomicFlowManager.Common
