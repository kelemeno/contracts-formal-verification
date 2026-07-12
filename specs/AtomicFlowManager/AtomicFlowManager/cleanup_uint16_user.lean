import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.cleanup_uint16_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_cleanup_uint16 (cleaned : Identifier) (value : Literal) (s₀ s₉ : State) : Prop := cleanup_uint16_concrete_of_code.1 cleaned value s₀ s₉

lemma cleanup_uint16_abs_of_concrete {s₀ s₉ : State} {cleaned value} :
  Spec (cleanup_uint16_concrete_of_code.1 cleaned value) s₀ s₉ →
  Spec (A_cleanup_uint16 cleaned value) s₀ s₉ := by
  intro h
  simpa [A_cleanup_uint16] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
