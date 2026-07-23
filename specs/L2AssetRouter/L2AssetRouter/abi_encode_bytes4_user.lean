import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes4_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_bytes4 (tail : Identifier) (headStart : Literal) (s₀ s₉ : State) : Prop := abi_encode_bytes4_concrete_of_code.1 tail headStart s₀ s₉

lemma abi_encode_bytes4_abs_of_concrete {s₀ s₉ : State} {tail headStart} :
  Spec (abi_encode_bytes4_concrete_of_code.1 tail headStart) s₀ s₉ →
  Spec (A_abi_encode_bytes4 tail headStart) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_bytes4] using h

end

end generated.L2AssetRouter.L2AssetRouter
