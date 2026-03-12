import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_8633753752739062557_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_8633753752739062557 (s₀ s₉ : State) : Prop :=
  if_8633753752739062557_concrete_of_code.1 s₀ s₉

lemma if_8633753752739062557_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8633753752739062557_concrete_of_code s₀ s₉ →
  Spec A_if_8633753752739062557 s₀ s₉ := by
  intro h
  simpa [A_if_8633753752739062557] using h

end

end L1AssetRouter.Common
