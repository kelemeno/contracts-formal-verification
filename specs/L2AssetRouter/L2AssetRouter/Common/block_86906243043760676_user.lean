import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.calldata_array_index_range_access_bytes_calldata_11819

import generated.L2AssetRouter.L2AssetRouter.Common.block_86906243043760676_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_86906243043760676 (s₀ s₉ : State) : Prop := block_86906243043760676_concrete_of_code.1 s₀ s₉

lemma block_86906243043760676_abs_of_concrete {s₀ s₉ : State} :
  Spec block_86906243043760676_concrete_of_code s₀ s₉ →
  Spec A_block_86906243043760676 s₀ s₉ := by
  intro h
  simpa [A_block_86906243043760676] using h

end

end L2AssetRouter.Common
