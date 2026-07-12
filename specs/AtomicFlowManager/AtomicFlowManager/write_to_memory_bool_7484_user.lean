import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool_7484_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_write_to_memory_bool_7484  (memPtr : Literal) (s₀ s₉ : State) : Prop := write_to_memory_bool_7484_concrete_of_code.1  memPtr s₀ s₉

lemma write_to_memory_bool_7484_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (write_to_memory_bool_7484_concrete_of_code.1  memPtr) s₀ s₉ →
  Spec (A_write_to_memory_bool_7484  memPtr) s₀ s₉ := by
  intro h
  simpa [A_write_to_memory_bool_7484] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
