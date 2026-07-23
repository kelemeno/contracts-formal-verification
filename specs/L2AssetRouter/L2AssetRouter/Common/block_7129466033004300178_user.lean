import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes

import generated.L2AssetRouter.L2AssetRouter.Common.block_7129466033004300178_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_7129466033004300178 (s₀ s₉ : State) : Prop := block_7129466033004300178_concrete_of_code.1 s₀ s₉

lemma block_7129466033004300178_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7129466033004300178_concrete_of_code s₀ s₉ →
  Spec A_block_7129466033004300178 s₀ s₉ := by
  intro h
  simpa [A_block_7129466033004300178] using h

end

end L2AssetRouter.Common
