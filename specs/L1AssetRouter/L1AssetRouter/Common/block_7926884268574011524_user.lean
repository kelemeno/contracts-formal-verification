import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_uint256_address_address

import generated.L1AssetRouter.L1AssetRouter.Common.block_7926884268574011524_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_block_7926884268574011524 (s₀ s₉ : State) : Prop := block_7926884268574011524_concrete_of_code.1 s₀ s₉

lemma block_7926884268574011524_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7926884268574011524_concrete_of_code s₀ s₉ →
  Spec A_block_7926884268574011524 s₀ s₉ := by
  intro h
  simpa [A_block_7926884268574011524] using h

end

end L1AssetRouter.Common
