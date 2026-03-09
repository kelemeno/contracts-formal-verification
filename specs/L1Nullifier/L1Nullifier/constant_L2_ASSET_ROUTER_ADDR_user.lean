import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.constant_L2_ASSET_ROUTER_ADDR_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_constant_L2_ASSET_ROUTER_ADDR (ret : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma constant_L2_ASSET_ROUTER_ADDR_abs_of_concrete {s₀ s₉ : State} {ret } :
  Spec (constant_L2_ASSET_ROUTER_ADDR_concrete_of_code.1 ret ) s₀ s₉ →
  Spec (A_constant_L2_ASSET_ROUTER_ADDR ret ) s₀ s₉ := by
  unfold constant_L2_ASSET_ROUTER_ADDR_concrete_of_code A_constant_L2_ASSET_ROUTER_ADDR
  sorry

end

end generated.L1Nullifier.L1Nullifier
