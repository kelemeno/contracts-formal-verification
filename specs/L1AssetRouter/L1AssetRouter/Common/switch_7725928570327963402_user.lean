import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address
import generated.L1AssetRouter.L1AssetRouter.Common.if_3829729205200461616
import generated.L1AssetRouter.L1AssetRouter.Common.if_1213823114410652249
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_4746309833740419612
import generated.L1AssetRouter.L1AssetRouter.Common.if_6347281329581904638

import generated.L1AssetRouter.L1AssetRouter.Common.switch_7725928570327963402_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_7725928570327963402 (s₀ s₉ : State) : Prop :=
  switch_7725928570327963402_concrete_of_code.1 s₀ s₉

lemma switch_7725928570327963402_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_7725928570327963402_concrete_of_code s₀ s₉ →
  Spec A_switch_7725928570327963402 s₀ s₉ := by
  intro h
  simpa [A_switch_7725928570327963402] using h

end

end L1AssetRouter.Common
