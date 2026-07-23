import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.abi_encode_bool_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_bool (tail : Identifier) (headStart value0 : Literal) (s₀ s₉ : State) : Prop := abi_encode_bool_concrete_of_code.1 tail headStart value0 s₀ s₉

lemma abi_encode_bool_abs_of_concrete {s₀ s₉ : State} {tail headStart value0} :
  Spec (abi_encode_bool_concrete_of_code.1 tail headStart value0) s₀ s₉ →
  Spec (A_abi_encode_bool tail headStart value0) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_bool] using h

end

end generated.L2AssetRouter.L2AssetRouter
