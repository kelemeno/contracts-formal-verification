import Clear.ReasoningPrinciple


import generated.DiamondProxy.DiamondProxy.Common.if_5048110242291525478_gen


namespace DiamondProxy.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_5048110242291525478 (s₀ s₉ : State) : Prop := sorry

lemma if_5048110242291525478_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5048110242291525478_concrete_of_code s₀ s₉ →
  Spec A_if_5048110242291525478 s₀ s₉ := by
  sorry

end

end DiamondProxy.Common
