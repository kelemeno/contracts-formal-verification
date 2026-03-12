import Clear.ReasoningPrinciple


import generated.DiamondProxy.DiamondProxy.extract_from_storage_value_offset_bool_gen


namespace generated.DiamondProxy.DiamondProxy

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- Extracts a bool from a packed storage slot: masks slot_value to 8 bits. -/
def A_extract_from_storage_value_offset_bool (value : Identifier) (slot_value : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦value ↦ Fin.land slot_value 255⟧

set_option maxHeartbeats 800000

lemma extract_from_storage_value_offset_bool_abs_of_concrete {{s₀ s₉ : State}} {value slot_value} :
  Spec (extract_from_storage_value_offset_bool_concrete_of_code.1 value slot_value) s₀ s₉ →
  Spec (A_extract_from_storage_value_offset_bool value slot_value) s₀ s₉ := by
  unfold extract_from_storage_value_offset_bool_concrete_of_code A_extract_from_storage_value_offset_bool
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMAnd'] at hconcrete
  symm
  simpa using hconcrete

end

end generated.DiamondProxy.DiamondProxy
