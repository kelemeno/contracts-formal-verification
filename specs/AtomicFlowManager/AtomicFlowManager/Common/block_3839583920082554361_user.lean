import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3839583920082554361_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_3839583920082554361 (s₀ s₉ : State) : Prop := block_3839583920082554361_concrete_of_code.1 s₀ s₉

lemma block_3839583920082554361_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3839583920082554361_concrete_of_code s₀ s₉ →
  Spec A_block_3839583920082554361 s₀ s₉ := by
  intro h
  simpa [A_block_3839583920082554361] using h

end

end AtomicFlowManager.Common
