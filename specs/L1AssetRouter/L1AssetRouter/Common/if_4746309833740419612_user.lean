import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address
import generated.L1AssetRouter.L1AssetRouter.Common.if_4617967422575755076
import generated.L1AssetRouter.L1AssetRouter.Common.if_1227481076126767289
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.if_4746309833740419612_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_4746309833740419612 (s₀ s₉ : State) : Prop := sorry

lemma if_4746309833740419612_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4746309833740419612_concrete_of_code s₀ s₉ →
  Spec A_if_4746309833740419612 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
