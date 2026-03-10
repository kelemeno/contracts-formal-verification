import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_238538577602929412
import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes
import generated.L1AssetRouter.L1AssetRouter.Common.if_6211710129036802204
import generated.L1AssetRouter.L1AssetRouter.Common.if_1974957643560532488
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.if_7118975047039834028_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_7118975047039834028 (s₀ s₉ : State) : Prop := sorry

lemma if_7118975047039834028_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7118975047039834028_concrete_of_code s₀ s₉ →
  Spec A_if_7118975047039834028 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
