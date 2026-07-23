import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_1947313727863088020
import generated.L2AssetRouter.L2AssetRouter.Common.block_4651535142338791594
import generated.L2AssetRouter.L2AssetRouter.Common.block_3266265886964482213
import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes_bytes32
import generated.L2AssetRouter.L2AssetRouter.Common.if_7069222774777857031
import generated.L2AssetRouter.L2AssetRouter.revert_forward
import generated.L2AssetRouter.L2AssetRouter.Common.if_3845449680979841486
import generated.L2AssetRouter.L2AssetRouter.finalize_allocation
import generated.L2AssetRouter.L2AssetRouter.abi_decode

import generated.L2AssetRouter.L2AssetRouter.Common.if_3497557402213865731_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_if_3497557402213865731 (s₀ s₉ : State) : Prop := if_3497557402213865731_concrete_of_code.1 s₀ s₉

lemma if_3497557402213865731_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3497557402213865731_concrete_of_code s₀ s₉ →
  Spec A_if_3497557402213865731 s₀ s₉ := by
  intro h
  simpa [A_if_3497557402213865731] using h

end

end L2AssetRouter.Common
