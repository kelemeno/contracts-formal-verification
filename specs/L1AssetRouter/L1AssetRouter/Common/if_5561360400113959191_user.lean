import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_5561360400113959191_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_5561360400113959191 (s₀ s₉ : State) : Prop :=
  if_5561360400113959191_concrete_of_code.1 s₀ s₉

lemma if_5561360400113959191_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5561360400113959191_concrete_of_code s₀ s₉ →
  Spec A_if_5561360400113959191 s₀ s₉ := by
  intro h
  simpa [A_if_5561360400113959191] using h

end

end L1AssetRouter.Common
