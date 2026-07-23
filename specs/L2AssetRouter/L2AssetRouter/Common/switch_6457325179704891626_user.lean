import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes32
import generated.L2AssetRouter.L2AssetRouter.Common.if_5520860426735255745
import generated.L2AssetRouter.L2AssetRouter.panic_error_0x11
import generated.L2AssetRouter.L2AssetRouter.Common.if_9101434560028777380
import generated.L2AssetRouter.L2AssetRouter.Common.if_7064732595386462372
import generated.L2AssetRouter.L2AssetRouter.convert_bytes20_to_address

import generated.L2AssetRouter.L2AssetRouter.Common.switch_6457325179704891626_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_switch_6457325179704891626 (s₀ s₉ : State) : Prop := switch_6457325179704891626_concrete_of_code.1 s₀ s₉

lemma switch_6457325179704891626_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_6457325179704891626_concrete_of_code s₀ s₉ →
  Spec A_switch_6457325179704891626 s₀ s₉ := by
  intro h
  simpa [A_switch_6457325179704891626] using h

end

end L2AssetRouter.Common
