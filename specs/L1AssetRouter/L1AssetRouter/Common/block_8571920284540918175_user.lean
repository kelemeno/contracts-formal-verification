import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.fun_encodeNTVAssetId

import generated.L1AssetRouter.L1AssetRouter.Common.block_8571920284540918175_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_block_8571920284540918175 (s₀ s₉ : State) : Prop := block_8571920284540918175_concrete_of_code.1 s₀ s₉

lemma block_8571920284540918175_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8571920284540918175_concrete_of_code s₀ s₉ →
  Spec A_block_8571920284540918175 s₀ s₉ := by
  intro h
  simpa [A_block_8571920284540918175] using h

end

end L1AssetRouter.Common
