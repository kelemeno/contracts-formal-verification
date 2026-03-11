import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.update_storage_value_offset_uint8_to_uint8_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- Sets byte 0 of storage slot 0 to 1 (clears byte 0 then ORs with 1). -/
def A_update_storage_value_offset_uint8_to_uint8  (s₀ s₉ : State) : Prop :=
  s₉ = s₀🇪⟦s₀.evm.sstore 0 (Fin.lor (Fin.land (s₀.evm.sload 0) (UInt256.lnot 255)) 1)⟧

set_option maxHeartbeats 800000

lemma update_storage_value_offset_uint8_to_uint8_abs_of_concrete {s₀ s₉ : State}  :
  Spec (update_storage_value_offset_uint8_to_uint8_concrete_of_code.1) s₀ s₉ →
  Spec (A_update_storage_value_offset_uint8_to_uint8) s₀ s₉ := by
  unfold update_storage_value_offset_uint8_to_uint8_concrete_of_code A_update_storage_value_offset_uint8_to_uint8
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMSload', EVMNot', EVMAnd', EVMOr', EVMSstore'] at hconcrete
  symm
  simpa using hconcrete

end

end generated.L1Nullifier.L1Nullifier
