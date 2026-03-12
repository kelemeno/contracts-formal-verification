import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.cleanup_uint16_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- cleanup_uint16 masks value to 16 bits (0xFFFF). -/
def A_cleanup_uint16 (cleaned : Identifier) (value : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦cleaned ↦ Fin.land value 65535⟧

set_option maxHeartbeats 800000

lemma cleanup_uint16_abs_of_concrete {s₀ s₉ : State} {cleaned value} :
  Spec (cleanup_uint16_concrete_of_code.1 cleaned value) s₀ s₉ →
  Spec (A_cleanup_uint16 cleaned value) s₀ s₉ := by
  unfold cleanup_uint16_concrete_of_code A_cleanup_uint16
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMAnd'] at hconcrete
  symm
  simpa using hconcrete

end

end generated.L1Nullifier.L1Nullifier
