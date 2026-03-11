import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.update_storage_value_offset_bool_to_bool_17751_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- Sets storage at slot, clearing byte 0 (mask with lnot(255)) and writing 1 (true at offset 0). -/
def A_update_storage_value_offset_bool_to_bool_17751 (slot : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = s₀🇪⟦s₀.evm.sstore slot (Fin.lor (Fin.land (s₀.evm.sload slot) (UInt256.lnot 255)) 1)⟧

set_option maxHeartbeats 800000

lemma update_storage_value_offset_bool_to_bool_17751_abs_of_concrete {s₀ s₉ : State} {slot} :
  Spec (update_storage_value_offset_bool_to_bool_17751_concrete_of_code.1 slot) s₀ s₉ →
  Spec (A_update_storage_value_offset_bool_to_bool_17751 slot) s₀ s₉ := by
  unfold update_storage_value_offset_bool_to_bool_17751_concrete_of_code A_update_storage_value_offset_bool_to_bool_17751
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMSload', EVMNot', EVMAnd', EVMOr', EVMSstore'] at hconcrete
  symm
  simpa using hconcrete

end

end generated.L1Nullifier.L1Nullifier
