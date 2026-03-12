import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset

import generated.L1AssetRouter.L1AssetRouter.Common.if_663842672556501099_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_if_663842672556501099 (s₀ s₉ : State) : Prop :=
  if_663842672556501099_concrete_of_code.1 s₀ s₉

lemma if_663842672556501099_abs_of_concrete {s₀ s₉ : State} :
  Spec if_663842672556501099_concrete_of_code s₀ s₉ →
  Spec A_if_663842672556501099 s₀ s₉ := by
  intro h
  simpa [A_if_663842672556501099] using h

end

end L1AssetRouter.Common
