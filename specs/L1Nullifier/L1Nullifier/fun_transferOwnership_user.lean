import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.fun_transferOwnership_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_fun_transferOwnership  (var_newOwner : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_transferOwnership_abs_of_concrete {s₀ s₉ : State} { var_newOwner} :
  Spec (fun_transferOwnership_concrete_of_code.1 var_newOwner) s₀ s₉ →
  Spec (A_fun_transferOwnership var_newOwner) s₀ s₉ := by
  unfold A_fun_transferOwnership
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
