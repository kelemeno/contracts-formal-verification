import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes_bytes32

import generated.L2AssetRouter.L2AssetRouter.Common.block_3266265886964482213_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_3266265886964482213 (s₀ s₉ : State) : Prop := block_3266265886964482213_concrete_of_code.1 s₀ s₉

lemma block_3266265886964482213_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3266265886964482213_concrete_of_code s₀ s₉ →
  Spec A_block_3266265886964482213 s₀ s₉ := by
  intro h
  simpa [A_block_3266265886964482213] using h

end

end L2AssetRouter.Common
