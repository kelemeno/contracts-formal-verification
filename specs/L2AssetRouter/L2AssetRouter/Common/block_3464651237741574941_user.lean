import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.require_helper_error_AssetIdNotSupported_bytes32
import generated.L2AssetRouter.L2AssetRouter.fun_burn
import generated.L2AssetRouter.L2AssetRouter.fun_encodeTxDataHash

import generated.L2AssetRouter.L2AssetRouter.Common.block_3464651237741574941_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_3464651237741574941 (s₀ s₉ : State) : Prop := block_3464651237741574941_concrete_of_code.1 s₀ s₉

lemma block_3464651237741574941_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3464651237741574941_concrete_of_code s₀ s₉ →
  Spec A_block_3464651237741574941 s₀ s₉ := by
  intro h
  simpa [A_block_3464651237741574941] using h

end

end L2AssetRouter.Common
