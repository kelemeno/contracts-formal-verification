import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_4418894817717783591
import generated.L1AssetRouter.L1AssetRouter.Common.if_5565014839478708744
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.switch_7882506306183545527
import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes
import generated.L1AssetRouter.L1AssetRouter.fun_verifyCallResultFromTarget
import generated.L1AssetRouter.L1AssetRouter.Common.if_3799284139383435799
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bool_fromMemory
import generated.L1AssetRouter.L1AssetRouter.Common.if_4979718963585679481
import generated.L1AssetRouter.L1AssetRouter.Common.if_6792581259599662798
import generated.L1AssetRouter.L1AssetRouter.Common.if_146527745671375149
import generated.L1AssetRouter.L1AssetRouter.Common.if_6175975206063726998
import generated.L1AssetRouter.L1AssetRouter.Common.if_4633911960071800862

import generated.L1AssetRouter.L1AssetRouter.Common.if_8334930945157384518_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_8334930945157384518 (s₀ s₉ : State) : Prop := sorry

lemma if_8334930945157384518_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8334930945157384518_concrete_of_code s₀ s₉ →
  Spec A_if_8334930945157384518 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
