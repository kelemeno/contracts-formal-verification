import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.abi_encode_uint256_bytes32_bytes32_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- ABI-encodes uint256 + bytes32 + bytes32: stores three values at consecutive 32-byte slots; tail = headStart + 96. -/
def abi_encode_uint256_bytes32_bytes32_evm (evm : EVM) (headStart value0 value1 value2 : Literal) : EVM :=
  (((evm.mstore headStart value0).mstore (headStart + 32) value1).mstore (headStart + 64) value2)

def A_abi_encode_uint256_bytes32_bytes32 (tail : Identifier) (headStart value0 value1 value2 : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = (s₀🇪⟦abi_encode_uint256_bytes32_bytes32_evm s₀.evm headStart value0 value1 value2⟧)⟦tail ↦ headStart + 96⟧

set_option maxHeartbeats 800000

lemma abi_encode_uint256_bytes32_bytes32_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2} :
  Spec (abi_encode_uint256_bytes32_bytes32_concrete_of_code.1 tail headStart value0 value1 value2) s₀ s₉ →
  Spec (A_abi_encode_uint256_bytes32_bytes32 tail headStart value0 value1 value2) s₀ s₉ := by
  unfold abi_encode_uint256_bytes32_bytes32_concrete_of_code A_abi_encode_uint256_bytes32_bytes32
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  symm
  simpa [abi_encode_uint256_bytes32_bytes32_evm] using hconcrete

end

end generated.L1AssetRouter.L1AssetRouter
