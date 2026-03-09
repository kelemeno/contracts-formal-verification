import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_5272959549066705990
import generated.L1AssetRouter.L1AssetRouter.Common.if_5587186783383625159
import generated.L1AssetRouter.L1AssetRouter.Common.if_3184704065110235532
import generated.L1AssetRouter.L1AssetRouter.Common.if_7867441904104493972
import generated.L1AssetRouter.L1AssetRouter.Common.if_3680740834951988335
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes

import generated.L1AssetRouter.L1AssetRouter.Common.switch_4369588892609084876_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_4369588892609084876 (s₀ s₉ : State) : Prop := sorry

lemma switch_4369588892609084876_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_4369588892609084876_concrete_of_code s₀ s₉ →
  Spec A_switch_4369588892609084876 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
