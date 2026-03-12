import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.abi_encode_bytes32_address_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- ABI-encodes bytes32 + address: stores value0 at offset 4, 160-bit masked value1 at offset 36; tail = 68. -/
def abi_encode_bytes32_address_evm (evm : EVM) (value0 value1 : Literal) : EVM :=
  (evm.mstore 4 value0).mstore 36 (Fin.land value1 (Fin.shiftLeft 1 160 - 1))

def A_abi_encode_bytes32_address (tail : Identifier) (value0 value1 : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = (s₀🇪⟦abi_encode_bytes32_address_evm s₀.evm value0 value1⟧)⟦tail ↦ 68⟧

set_option maxHeartbeats 800000

lemma abi_encode_bytes32_address_abs_of_concrete {s₀ s₉ : State} {tail value0 value1} :
  Spec (abi_encode_bytes32_address_concrete_of_code.1 tail value0 value1) s₀ s₉ →
  Spec (A_abi_encode_bytes32_address tail value0 value1) s₀ s₉ := by
  unfold abi_encode_bytes32_address_concrete_of_code A_abi_encode_bytes32_address
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  symm
  simpa [abi_encode_bytes32_address_evm] using hconcrete

end

end generated.L1Nullifier.L1Nullifier
