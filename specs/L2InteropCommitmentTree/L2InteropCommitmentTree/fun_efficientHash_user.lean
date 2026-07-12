import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_fun_efficientHash (var_result : Identifier) (var_lhs var_rhs : Literal) (s₀ s₉ : State) : Prop := fun_efficientHash_concrete_of_code.1 var_result var_lhs var_rhs s₀ s₉

lemma fun_efficientHash_abs_of_concrete {s₀ s₉ : State} {var_result var_lhs var_rhs} :
  Spec (fun_efficientHash_concrete_of_code.1 var_result var_lhs var_rhs) s₀ s₉ →
  Spec (A_fun_efficientHash var_result var_lhs var_rhs) s₀ s₉ := by
  intro h
  simpa [A_fun_efficientHash] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
