import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.write_to_memory_address_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- write_to_memory_address stores value masked to 160 bits at memPtr. -/
def A_write_to_memory_address (memPtr value : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = s₀🇪⟦s₀.evm.mstore memPtr (Fin.land value (Fin.shiftLeft 1 160 - 1))⟧

set_option maxHeartbeats 800000

lemma write_to_memory_address_abs_of_concrete {s₀ s₉ : State} {memPtr value} :
  Spec (write_to_memory_address_concrete_of_code.1 memPtr value) s₀ s₉ →
  Spec (A_write_to_memory_address memPtr value) s₀ s₉ := by
  unfold write_to_memory_address_concrete_of_code A_write_to_memory_address
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMShl', EVMSub', EVMAnd', EVMMstore'] at hconcrete
  symm
  simpa using hconcrete

end

end generated.L1Nullifier.L1Nullifier
