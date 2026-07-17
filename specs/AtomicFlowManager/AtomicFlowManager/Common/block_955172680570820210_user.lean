import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_955172680570820210_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_955172680570820210 (s₀ s₉ : State) : Prop := sorry

lemma block_955172680570820210_abs_of_concrete {s₀ s₉ : State} :
  Spec block_955172680570820210_concrete_of_code s₀ s₉ →
  Spec A_block_955172680570820210 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
