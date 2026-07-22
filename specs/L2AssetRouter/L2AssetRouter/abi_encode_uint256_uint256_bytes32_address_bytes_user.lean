import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_5568105450979583177
import generated.L2AssetRouter.L2AssetRouter.Common.block_852090862156783339
import generated.L2AssetRouter.L2AssetRouter.Common.block_7129466033004300178
import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes

import generated.L2AssetRouter.L2AssetRouter.abi_encode_uint256_uint256_bytes32_address_bytes_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_abi_encode_uint256_uint256_bytes32_address_bytes (tail : Identifier) (headStart value0 value1 value2 value3 value4 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_uint256_uint256_bytes32_address_bytes_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2 value3 value4} :
  Spec (abi_encode_uint256_uint256_bytes32_address_bytes_concrete_of_code.1 tail headStart value0 value1 value2 value3 value4) s₀ s₉ →
  Spec (A_abi_encode_uint256_uint256_bytes32_address_bytes tail headStart value0 value1 value2 value3 value4) s₀ s₉ := by
  unfold abi_encode_uint256_uint256_bytes32_address_bytes_concrete_of_code A_abi_encode_uint256_uint256_bytes32_address_bytes
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
