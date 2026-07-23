import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_3548837307886077614
import generated.L2AssetRouter.L2AssetRouter.Common.block_3803473238725326670

import generated.L2AssetRouter.L2AssetRouter.Common.if_8590281706542830210_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_if_8590281706542830210 (s₀ s₉ : State) : Prop := if_8590281706542830210_concrete_of_code.1 s₀ s₉

lemma if_8590281706542830210_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8590281706542830210_concrete_of_code s₀ s₉ →
  Spec A_if_8590281706542830210 s₀ s₉ := by
  intro h
  simpa [A_if_8590281706542830210] using h

end

end L2AssetRouter.Common
