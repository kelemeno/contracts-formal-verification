import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_6480247248308923535
import generated.L2AssetRouter.L2AssetRouter.finalize_allocation
import generated.L2AssetRouter.L2AssetRouter.abi_decode_bytes32_fromMemory

import generated.L2AssetRouter.L2AssetRouter.Common.if_5771020514989660505_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_if_5771020514989660505 (s₀ s₉ : State) : Prop := if_5771020514989660505_concrete_of_code.1 s₀ s₉

lemma if_5771020514989660505_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5771020514989660505_concrete_of_code s₀ s₉ →
  Spec A_if_5771020514989660505 s₀ s₉ := by
  intro h
  simpa [A_if_5771020514989660505] using h

end

end L2AssetRouter.Common
