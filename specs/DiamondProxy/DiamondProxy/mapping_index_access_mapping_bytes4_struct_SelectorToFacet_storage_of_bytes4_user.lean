import Clear.ReasoningPrinciple


import generated.DiamondProxy.DiamondProxy.mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4_gen


namespace generated.DiamondProxy.DiamondProxy

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- Computes the storage slot for a bytes4 -> SelectorToFacet mapping entry using keccak256(abi.encode(key_masked, base_slot)). -/
def A_mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4 (dataSlot : Identifier) (key : Literal) (s₀ s₉ : State) : Prop :=
  let evm1 := (s₀.evm.mstore 0 (Fin.land key (Fin.shiftLeft 4294967295 224))).mstore 32
    90909012999857140622417080374671856515688564136957639390032885430481714942747
  match evm1.keccak256 0 64 with
  | .some (hash, evm2) => s₉ = (s₀🇪⟦evm2⟧)⟦dataSlot ↦ hash⟧
  | .none => True

set_option maxHeartbeats 800000

lemma mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4_abs_of_concrete {s₀ s₉ : State} {dataSlot key} :
  Spec (mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4_concrete_of_code.1 dataSlot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4 dataSlot key) s₀ s₉ := by
  unfold mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4_concrete_of_code
    A_mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMMstore', EVMShl', EVMAnd', EVMKeccak256'] at hconcrete
  rcases h : ((evm.mstore 0 (Fin.land key (Fin.shiftLeft 4294967295 224))).mstore 32
    90909012999857140622417080374671856515688564136957639390032885430481714942747).keccak256 0 64 with
  | .some ⟨hash, evm2⟩ =>
    simp only [h] at hconcrete ⊢
    simpa [State.setEvm] using hconcrete.symm
  | .none =>
    trivial

end

end generated.DiamondProxy.DiamondProxy
