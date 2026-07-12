import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5690683828684622158_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_5690683828684622158 (s₀ s₉ : State) : Prop := block_5690683828684622158_concrete_of_code.1 s₀ s₉

lemma block_5690683828684622158_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5690683828684622158_concrete_of_code s₀ s₉ →
  Spec A_block_5690683828684622158 s₀ s₉ := by
  intro h
  simpa [A_block_5690683828684622158] using h

end

end AtomicFlowManager.Common
