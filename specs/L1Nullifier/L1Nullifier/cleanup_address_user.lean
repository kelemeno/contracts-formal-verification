import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.cleanup_address_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Address mask: keeps only the lower 160 bits (20 bytes). -/
def addressMask : UInt256 := Fin.shiftLeft 1 160 - 1

/-- cleanup_address masks value to the lower 160 bits (EVM address width). -/
def A_cleanup_address (cleaned : Identifier) (value : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦cleaned ↦ Fin.land value addressMask⟧

set_option maxHeartbeats 800000

lemma cleanup_address_abs_of_concrete {s₀ s₉ : State} {cleaned value} :
  Spec (cleanup_address_concrete_of_code.1 cleaned value) s₀ s₉ →
  Spec (A_cleanup_address cleaned value) s₀ s₉ := by
  unfold cleanup_address_concrete_of_code A_cleanup_address
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMShl', EVMSub', EVMAnd'] at hconcrete
  symm
  simpa [addressMask] using hconcrete

end

end generated.L1Nullifier.L1Nullifier
