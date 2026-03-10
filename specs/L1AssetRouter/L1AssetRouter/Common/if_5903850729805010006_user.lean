import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_5903850729805010006_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_5903850729805010006 (s₀ s₉ : State) : Prop := sorry

lemma if_5903850729805010006_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5903850729805010006_concrete_of_code s₀ s₉ →
  Spec A_if_5903850729805010006 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
