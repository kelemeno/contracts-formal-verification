import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.mcopy

import generated.L1AssetRouter.L1AssetRouter.Common.switch_8800258257933484115_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_switch_8800258257933484115 (s₀ s₉ : State) : Prop := sorry

lemma switch_8800258257933484115_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8800258257933484115_concrete_of_code s₀ s₉ →
  Spec A_switch_8800258257933484115 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
