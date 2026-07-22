import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_3333394244207705370
import generated.L2AssetRouter.L2AssetRouter.array_allocation_size_bytes
import generated.L2AssetRouter.L2AssetRouter.finalize_allocation
import generated.L2AssetRouter.L2AssetRouter.Common.block_8210404315093443709

import generated.L2AssetRouter.L2AssetRouter.Common.switch_3088111385004876443_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_switch_3088111385004876443 (s₀ s₉ : State) : Prop := sorry

lemma switch_3088111385004876443_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_3088111385004876443_concrete_of_code s₀ s₉ →
  Spec A_switch_3088111385004876443 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
