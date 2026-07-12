import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_uncheckedInc_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_fun_uncheckedInc (var_ : Identifier) (var_number : Literal) (s₀ s₉ : State) : Prop := fun_uncheckedInc_concrete_of_code.1 var_ var_number s₀ s₉

lemma fun_uncheckedInc_abs_of_concrete {s₀ s₉ : State} {var_ var_number} :
  Spec (fun_uncheckedInc_concrete_of_code.1 var_ var_number) s₀ s₉ →
  Spec (A_fun_uncheckedInc var_ var_number) s₀ s₉ := by
  intro h
  simpa [A_fun_uncheckedInc] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
