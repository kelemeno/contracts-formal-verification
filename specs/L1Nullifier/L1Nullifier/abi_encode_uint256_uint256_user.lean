import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.abi_encode_uint256_uint256_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- ABI-encodes two uint256 values at headStart and headStart+32; tail = headStart + 64. -/
def abi_encode_uint256_uint256_evm (evm : EVM) (headStart value0 value1 : Literal) : EVM :=
  (evm.mstore headStart value0).mstore (headStart + 32) value1

def A_abi_encode_uint256_uint256 (tail : Identifier) (headStart value0 value1 : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = (s₀🇪⟦abi_encode_uint256_uint256_evm s₀.evm headStart value0 value1⟧)⟦tail ↦ headStart + 64⟧

set_option maxHeartbeats 800000

lemma abi_encode_uint256_uint256_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1} :
  Spec (abi_encode_uint256_uint256_concrete_of_code.1 tail headStart value0 value1) s₀ s₉ →
  Spec (A_abi_encode_uint256_uint256 tail headStart value0 value1) s₀ s₉ := by
  unfold abi_encode_uint256_uint256_concrete_of_code A_abi_encode_uint256_uint256
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  symm
  simpa [abi_encode_uint256_uint256_evm] using hconcrete

end

end generated.L1Nullifier.L1Nullifier
