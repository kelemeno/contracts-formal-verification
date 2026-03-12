import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.read_from_storage_split_offset_bool_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- Reads a bool from storage at slot: returns sload(slot) masked to 8 bits. -/
def A_read_from_storage_split_offset_bool (value : Identifier) (slot : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦value ↦ Fin.land (s₀.evm.sload slot) 255⟧

set_option maxHeartbeats 800000

lemma read_from_storage_split_offset_bool_abs_of_concrete {{s₀ s₉ : State}} {value slot} :
  Spec (read_from_storage_split_offset_bool_concrete_of_code.1 value slot) s₀ s₉ →
  Spec (A_read_from_storage_split_offset_bool value slot) s₀ s₉ := by
  unfold read_from_storage_split_offset_bool_concrete_of_code A_read_from_storage_split_offset_bool
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMSload', EVMAnd'] at hconcrete
  symm
  simpa using hconcrete

end

end generated.L1Nullifier.L1Nullifier
