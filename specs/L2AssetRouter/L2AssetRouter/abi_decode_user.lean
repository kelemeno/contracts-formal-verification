import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_7555350692620246630

import generated.L2AssetRouter.L2AssetRouter.abi_decode_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_abi_decode  (headStart dataEnd : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_abs_of_concrete {s₀ s₉ : State} { headStart dataEnd} :
  Spec (abi_decode_concrete_of_code.1  headStart dataEnd) s₀ s₉ →
  Spec (A_abi_decode  headStart dataEnd) s₀ s₉ := by
  unfold abi_decode_concrete_of_code A_abi_decode
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
