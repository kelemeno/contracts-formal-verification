import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.fun_isContract_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_fun_isContract (var : Identifier) (var_account : Literal) (s₀ s₉ : State) : Prop := fun_isContract_concrete_of_code.1 var var_account s₀ s₉

lemma fun_isContract_abs_of_concrete {s₀ s₉ : State} {var var_account} :
  Spec (fun_isContract_concrete_of_code.1 var var_account) s₀ s₉ →
  Spec (A_fun_isContract var var_account) s₀ s₉ := by
  intro h
  simpa [A_fun_isContract] using h

end

end generated.L1Nullifier.L1Nullifier
