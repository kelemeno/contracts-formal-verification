import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.switch_4762451955261439273_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_switch_4762451955261439273 (s₀ s₉ : State) : Prop :=
  switch_4762451955261439273_concrete_of_code.1 s₀ s₉

lemma switch_4762451955261439273_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_4762451955261439273_concrete_of_code s₀ s₉ →
  Spec A_switch_4762451955261439273 s₀ s₉ := by
  intro h
  simpa [A_switch_4762451955261439273] using h

end

end L1AssetRouter.Common
