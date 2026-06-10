import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.fun_transferOwnership_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_fun_transferOwnership  (var_newOwner : Literal) (s₀ s₉ : State) : Prop := fun_transferOwnership_concrete_of_code.1  var_newOwner s₀ s₉

lemma fun_transferOwnership_abs_of_concrete {s₀ s₉ : State} { var_newOwner} :
  Spec (fun_transferOwnership_concrete_of_code.1  var_newOwner) s₀ s₉ →
  Spec (A_fun_transferOwnership  var_newOwner) s₀ s₉ := by
  intro h
  simpa [A_fun_transferOwnership] using h

end

end generated.L1Nullifier.L1Nullifier
