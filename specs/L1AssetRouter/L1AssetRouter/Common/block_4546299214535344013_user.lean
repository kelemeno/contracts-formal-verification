import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.block_4546299214535344013_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_block_4546299214535344013 (s₀ s₉ : State) : Prop := block_4546299214535344013_concrete_of_code.1 s₀ s₉

lemma block_4546299214535344013_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4546299214535344013_concrete_of_code s₀ s₉ →
  Spec A_block_4546299214535344013 s₀ s₉ := by
  intro h
  simpa [A_block_4546299214535344013] using h

end

end L1AssetRouter.Common
