import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.revert_forward_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_revert_forward   (s₀ s₉ : State) : Prop := sorry

lemma revert_forward_abs_of_concrete {s₀ s₉ : State}  :
  Spec (revert_forward_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_revert_forward  ) s₀ s₉ := by
  unfold revert_forward_concrete_of_code A_revert_forward
  sorry

end

end generated.L1Nullifier.L1Nullifier
