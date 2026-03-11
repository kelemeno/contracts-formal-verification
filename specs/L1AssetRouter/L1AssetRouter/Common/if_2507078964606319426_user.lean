import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_5438789511991820537

import generated.L1AssetRouter.L1AssetRouter.Common.if_2507078964606319426_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_if_2507078964606319426 (s₀ s₉ : State) : Prop :=
  if_2507078964606319426_concrete_of_code.1 s₀ s₉

lemma if_2507078964606319426_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2507078964606319426_concrete_of_code s₀ s₉ →
  Spec A_if_2507078964606319426 s₀ s₉ := by
  intro h
  simpa [A_if_2507078964606319426] using h

end

end L1AssetRouter.Common
