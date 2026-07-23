import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_242142322673774145_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_242142322673774145 (s₀ s₉ : State) : Prop := block_242142322673774145_concrete_of_code.1 s₀ s₉

lemma block_242142322673774145_abs_of_concrete {s₀ s₉ : State} :
  Spec block_242142322673774145_concrete_of_code s₀ s₉ →
  Spec A_block_242142322673774145 s₀ s₉ := by
  intro h
  simpa [A_block_242142322673774145] using h

end

end AtomicFlowManager.Common
