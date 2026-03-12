import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.panic_error_0x41_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_panic_error_0x41   (s₀ s₉ : State) : Prop :=
  panic_error_0x41_concrete_of_code.1 s₀ s₉

lemma panic_error_0x41_abs_of_concrete {s₀ s₉ : State} :
  Spec (panic_error_0x41_concrete_of_code.1 ) s₀ s₉ →
  Spec (A_panic_error_0x41 ) s₀ s₉ := by
  intro h
  simpa [A_panic_error_0x41] using h

end

end generated.L1Nullifier.L1Nullifier
