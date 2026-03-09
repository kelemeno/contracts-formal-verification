import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.write_to_memory_bool_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_write_to_memory_bool  (memPtr : Literal) (s₀ s₉ : State) : Prop := sorry

lemma write_to_memory_bool_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (write_to_memory_bool_concrete_of_code.1  memPtr) s₀ s₉ →
  Spec (A_write_to_memory_bool  memPtr) s₀ s₉ := by
  unfold write_to_memory_bool_concrete_of_code A_write_to_memory_bool
  sorry

end

end generated.L1Nullifier.L1Nullifier
