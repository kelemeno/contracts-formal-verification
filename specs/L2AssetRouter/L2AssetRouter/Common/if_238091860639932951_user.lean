import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_453708579015761283
import generated.L2AssetRouter.L2AssetRouter.Common.block_8512115908049072329
import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes_calldata_to_bytes

import generated.L2AssetRouter.L2AssetRouter.Common.if_238091860639932951_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_if_238091860639932951 (s₀ s₉ : State) : Prop := if_238091860639932951_concrete_of_code.1 s₀ s₉

lemma if_238091860639932951_abs_of_concrete {s₀ s₉ : State} :
  Spec if_238091860639932951_concrete_of_code s₀ s₉ →
  Spec A_if_238091860639932951 s₀ s₉ := by
  intro h
  simpa [A_if_238091860639932951] using h

end

end L2AssetRouter.Common
