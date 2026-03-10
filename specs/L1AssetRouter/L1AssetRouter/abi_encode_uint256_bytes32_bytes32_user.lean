import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.abi_encode_uint256_bytes32_bytes32_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_uint256_bytes32_bytes32 (tail : Identifier) (headStart value0 value1 value2 : Literal) (s₀ s₉ : State) : Prop := True

lemma abi_encode_uint256_bytes32_bytes32_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2} :
  Spec (abi_encode_uint256_bytes32_bytes32_concrete_of_code.1 tail headStart value0 value1 value2) s₀ s₉ →
  Spec (A_abi_encode_uint256_bytes32_bytes32 tail headStart value0 value1 value2) s₀ s₉ := by
  unfold abi_encode_uint256_bytes32_bytes32_concrete_of_code A_abi_encode_uint256_bytes32_bytes32
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1AssetRouter.L1AssetRouter
