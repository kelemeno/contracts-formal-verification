import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.if_4635858785563542990_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_if_4635858785563542990 (s₀ s₉ : State) : Prop :=
  if_4635858785563542990_concrete_of_code.1 s₀ s₉

lemma if_4635858785563542990_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4635858785563542990_concrete_of_code s₀ s₉ →
  Spec A_if_4635858785563542990 s₀ s₉ := by
  intro h
  simpa [A_if_4635858785563542990] using h

end

end L1AssetRouter.Common
