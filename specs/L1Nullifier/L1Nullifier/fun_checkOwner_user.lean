import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.fun_checkOwner_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_fun_checkOwner   (s₀ s₉ : State) : Prop := True

lemma fun_checkOwner_abs_of_concrete {s₀ s₉ : State} :
  Spec (fun_checkOwner_concrete_of_code.1 ) s₀ s₉ →
  Spec (A_fun_checkOwner ) s₀ s₉ := by
  unfold A_fun_checkOwner
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
