import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes_calldata

import generated.L1AssetRouter.L1AssetRouter.abi_encode_uint256_bytes32_bytes_calldata_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_abi_encode_uint256_bytes32_bytes_calldata (tail : Identifier) (headStart value0 value1 value2 value3 : Literal) (s₀ s₉ : State) : Prop :=
  abi_encode_uint256_bytes32_bytes_calldata_concrete_of_code.1 tail headStart value0 value1 value2 value3 s₀ s₉

lemma abi_encode_uint256_bytes32_bytes_calldata_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2 value3} :
  Spec (abi_encode_uint256_bytes32_bytes_calldata_concrete_of_code.1 tail headStart value0 value1 value2 value3) s₀ s₉ →
  Spec (A_abi_encode_uint256_bytes32_bytes_calldata tail headStart value0 value1 value2 value3) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_uint256_bytes32_bytes_calldata] using h

end

end generated.L1AssetRouter.L1AssetRouter
