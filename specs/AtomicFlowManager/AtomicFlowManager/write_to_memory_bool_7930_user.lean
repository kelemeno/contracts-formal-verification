import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool_7930_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_write_to_memory_bool_7930  (memPtr : Literal) (s₀ s₉ : State) : Prop := write_to_memory_bool_7930_concrete_of_code.1 memPtr s₀ s₉

lemma write_to_memory_bool_7930_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (write_to_memory_bool_7930_concrete_of_code.1  memPtr) s₀ s₉ →
  Spec (A_write_to_memory_bool_7930  memPtr) s₀ s₉ := by
  unfold write_to_memory_bool_7930_concrete_of_code A_write_to_memory_bool_7930
  intro h
  simpa [A_write_to_memory_bool_7930] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
