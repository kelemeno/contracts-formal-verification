import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.constant_L2_BRIDGEHUB_ADDR_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_constant_L2_BRIDGEHUB_ADDR (ret : Identifier)  (s₀ s₉ : State) : Prop := constant_L2_BRIDGEHUB_ADDR_concrete_of_code.1 ret s₀ s₉

lemma constant_L2_BRIDGEHUB_ADDR_abs_of_concrete {s₀ s₉ : State} {ret } :
  Spec (constant_L2_BRIDGEHUB_ADDR_concrete_of_code.1 ret ) s₀ s₉ →
  Spec (A_constant_L2_BRIDGEHUB_ADDR ret ) s₀ s₉ := by
  intro h
  simpa [A_constant_L2_BRIDGEHUB_ADDR] using h

end

end generated.L2AssetRouter.L2AssetRouter
