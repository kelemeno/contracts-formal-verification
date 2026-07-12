import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_panic_error_0x41   (s₀ s₉ : State) : Prop := panic_error_0x41_concrete_of_code.1 s₀ s₉

lemma panic_error_0x41_abs_of_concrete {s₀ s₉ : State}  :
  Spec (panic_error_0x41_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_panic_error_0x41  ) s₀ s₉ := by
  intro h
  simpa [A_panic_error_0x41] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
