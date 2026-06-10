import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_238538577602929412
import generated.L1AssetRouter.L1AssetRouter.Common.block_852842547833696019
import generated.L1AssetRouter.L1AssetRouter.Common.block_6830749755316520918
import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes
import generated.L1AssetRouter.L1AssetRouter.Common.block_7742332354904808350
import generated.L1AssetRouter.L1AssetRouter.Common.if_6211710129036802204
import generated.L1AssetRouter.L1AssetRouter.Common.if_1974957643560532488
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.if_7093463299791269861_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_7093463299791269861 (s₀ s₉ : State) : Prop := if_7093463299791269861_concrete_of_code.1 s₀ s₉

lemma if_7093463299791269861_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7093463299791269861_concrete_of_code s₀ s₉ →
  Spec A_if_7093463299791269861 s₀ s₉ := by
  intro h
  simpa [A_if_7093463299791269861] using h

end

end L1AssetRouter.Common
