import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.abi_decode_uint256_17641_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- abi_decode_uint256_17641 loads a uint256 from calldata at offset 36. -/
def A_abi_decode_uint256_17641 (value : Identifier) (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦value ↦ s₀.evm.calldataload 36⟧

set_option maxHeartbeats 800000

lemma abi_decode_uint256_17641_abs_of_concrete {{s₀ s₉ : State}} {{value}} :
  Spec (abi_decode_uint256_17641_concrete_of_code.1 value) s₀ s₉ →
  Spec (A_abi_decode_uint256_17641 value) s₀ s₉ := by
  unfold abi_decode_uint256_17641_concrete_of_code A_abi_decode_uint256_17641
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMCalldataload'] at hconcrete
  symm
  simpa using hconcrete

end

end generated.L1Nullifier.L1Nullifier
