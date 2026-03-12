import Clear.ReasoningPrinciple


import generated.DiamondProxy.DiamondProxy.extract_from_storage_value_offset_address_gen


namespace generated.DiamondProxy.DiamondProxy

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- Extracts an address from a packed storage slot: masks slot_value to 160 bits. -/
def A_extract_from_storage_value_offset_address (value : Identifier) (slot_value : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦value ↦ Fin.land slot_value (Fin.shiftLeft 1 160 - 1)⟧

set_option maxHeartbeats 800000

lemma extract_from_storage_value_offset_address_abs_of_concrete {{s₀ s₉ : State}} {value slot_value} :
  Spec (extract_from_storage_value_offset_address_concrete_of_code.1 value slot_value) s₀ s₉ →
  Spec (A_extract_from_storage_value_offset_address value slot_value) s₀ s₉ := by
  unfold extract_from_storage_value_offset_address_concrete_of_code A_extract_from_storage_value_offset_address
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMShl', EVMSub', EVMAnd'] at hconcrete
  symm
  simpa using hconcrete

end

end generated.DiamondProxy.DiamondProxy
