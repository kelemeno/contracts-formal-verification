import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- Computes nested mapping storage slot: keccak256(abi.encode(key, slot)) -/
def A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256 (dataSlot : Identifier) (slot key : Literal) (s₀ s₉ : State) : Prop :=
  let evm1 := (s₀.evm.mstore 0 key).mstore 32 slot
  match evm1.keccak256 0 64 with
  | .some (hash, evm2) => s₉ = (s₀🇪⟦evm2⟧)⟦dataSlot ↦ hash⟧
  | .none => True

set_option maxHeartbeats 800000

lemma mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_abs_of_concrete {{s₀ s₉ : State}} {dataSlot slot key} :
  Spec (mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_concrete_of_code.1 dataSlot slot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256 dataSlot slot key) s₀ s₉ := by
  unfold mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_concrete_of_code A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMMstore', EVMAnd', EVMShl', EVMSub', EVMKeccak256'] at hconcrete
  rcases h : (evm.mstore 0 key).mstore 32 slot.keccak256 0 64 with
  | .some ⟨hash, evm2⟩ =>
    simp only [h] at hconcrete ⊢
    simpa [State.setEvm] using hconcrete.symm
  | .none =>
    trivial

end

end generated.L1Nullifier.L1Nullifier
