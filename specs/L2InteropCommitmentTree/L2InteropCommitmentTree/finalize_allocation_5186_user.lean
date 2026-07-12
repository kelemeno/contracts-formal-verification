import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation_5186_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_finalize_allocation_5186   (s₀ s₉ : State) : Prop := finalize_allocation_5186_concrete_of_code.1 s₀ s₉

lemma finalize_allocation_5186_abs_of_concrete {s₀ s₉ : State}  :
  Spec (finalize_allocation_5186_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_finalize_allocation_5186  ) s₀ s₉ := by
  intro h
  simpa [A_finalize_allocation_5186] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
