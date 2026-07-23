import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.abi_encode_uint256_bytes32_bytes_calldata

import generated.L2AssetRouter.L2AssetRouter.Common.block_6459688961663567866_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_6459688961663567866 (s₀ s₉ : State) : Prop := block_6459688961663567866_concrete_of_code.1 s₀ s₉

lemma block_6459688961663567866_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6459688961663567866_concrete_of_code s₀ s₉ →
  Spec A_block_6459688961663567866 s₀ s₉ := by
  intro h
  simpa [A_block_6459688961663567866] using h

end

end L2AssetRouter.Common
