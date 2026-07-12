import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_address_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_write_to_memory_address  (memPtr value : Literal) (s₀ s₉ : State) : Prop := write_to_memory_address_concrete_of_code.1  memPtr value s₀ s₉

lemma write_to_memory_address_abs_of_concrete {s₀ s₉ : State} { memPtr value} :
  Spec (write_to_memory_address_concrete_of_code.1  memPtr value) s₀ s₉ →
  Spec (A_write_to_memory_address  memPtr value) s₀ s₉ := by
  intro h
  simpa [A_write_to_memory_address] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
