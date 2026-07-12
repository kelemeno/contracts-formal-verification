import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.cleanup_bool_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_cleanup_bool (cleaned : Identifier) (value : Literal) (s₀ s₉ : State) : Prop := cleanup_bool_concrete_of_code.1 cleaned value s₀ s₉

lemma cleanup_bool_abs_of_concrete {s₀ s₉ : State} {cleaned value} :
  Spec (cleanup_bool_concrete_of_code.1 cleaned value) s₀ s₉ →
  Spec (A_cleanup_bool cleaned value) s₀ s₉ := by
  intro h
  simpa [A_cleanup_bool] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
