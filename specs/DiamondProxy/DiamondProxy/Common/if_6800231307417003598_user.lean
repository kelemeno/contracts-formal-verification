import Clear.ReasoningPrinciple


import generated.DiamondProxy.DiamondProxy.Common.if_6800231307417003598_gen


namespace DiamondProxy.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_6800231307417003598 (s₀ s₉ : State) : Prop := sorry

lemma if_6800231307417003598_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6800231307417003598_concrete_of_code s₀ s₉ →
  Spec A_if_6800231307417003598 s₀ s₉ := by
  sorry

end

end DiamondProxy.Common
