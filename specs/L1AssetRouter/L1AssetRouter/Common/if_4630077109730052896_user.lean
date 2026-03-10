import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_4630077109730052896_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_4630077109730052896 (s₀ s₉ : State) : Prop := sorry

lemma if_4630077109730052896_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4630077109730052896_concrete_of_code s₀ s₉ →
  Spec A_if_4630077109730052896 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
