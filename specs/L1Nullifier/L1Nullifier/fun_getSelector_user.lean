import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.fun_getSelector_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_fun_getSelector (var : Identifier) (var__data_mpos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_getSelector_abs_of_concrete {s₀ s₉ : State} {var var__data_mpos} :
  Spec (fun_getSelector_concrete_of_code.1 var var__data_mpos) s₀ s₉ →
  Spec (A_fun_getSelector var var__data_mpos) s₀ s₉ := by
  unfold fun_getSelector_concrete_of_code A_fun_getSelector
  sorry

end

end generated.L1Nullifier.L1Nullifier
