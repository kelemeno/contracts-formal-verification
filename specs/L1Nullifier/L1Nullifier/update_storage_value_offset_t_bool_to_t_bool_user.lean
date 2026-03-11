import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.update_storage_value_offset_t_bool_to_t_bool_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- Clears bits 8-15 of storage slot 0 (writes false/zero at byte offset 8). -/
def A_update_storage_value_offset_t_bool_to_t_bool  (s₀ s₉ : State) : Prop :=
  s₉ = s₀🇪⟦s₀.evm.sstore 0 (Fin.land (s₀.evm.sload 0) (UInt256.lnot 65280))⟧

set_option maxHeartbeats 800000

lemma update_storage_value_offset_t_bool_to_t_bool_abs_of_concrete {s₀ s₉ : State}  :
  Spec (update_storage_value_offset_t_bool_to_t_bool_concrete_of_code.1) s₀ s₉ →
  Spec (A_update_storage_value_offset_t_bool_to_t_bool) s₀ s₉ := by
  unfold update_storage_value_offset_t_bool_to_t_bool_concrete_of_code A_update_storage_value_offset_t_bool_to_t_bool
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMSload', EVMNot', EVMAnd', EVMSstore'] at hconcrete
  symm
  simpa using hconcrete

end

end generated.L1Nullifier.L1Nullifier
