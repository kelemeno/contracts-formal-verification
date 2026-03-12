import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes

import generated.L1AssetRouter.L1AssetRouter.Common.switch_5144273952670483922_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_switch_5144273952670483922 (s₀ s₉ : State) : Prop :=
  switch_5144273952670483922_concrete_of_code.1 s₀ s₉

lemma switch_5144273952670483922_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_5144273952670483922_concrete_of_code s₀ s₉ →
  Spec A_switch_5144273952670483922 s₀ s₉ := by
  intro h
  simpa [A_switch_5144273952670483922] using h

end

end L1AssetRouter.Common
