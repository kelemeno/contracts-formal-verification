import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.cleanup_bool_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_cleanup_bool (cleaned : Identifier) (value : Literal) (s₀ s₉ : State) : Prop := True

lemma cleanup_bool_abs_of_concrete {s₀ s₉ : State} {cleaned value} :
  Spec (cleanup_bool_concrete_of_code.1 cleaned value) s₀ s₉ →
  Spec (A_cleanup_bool cleaned value) s₀ s₉ := by
  unfold A_cleanup_bool
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
