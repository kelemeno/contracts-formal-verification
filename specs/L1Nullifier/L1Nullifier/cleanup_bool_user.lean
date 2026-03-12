import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.cleanup_bool_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- cleanup_bool normalizes a value to 0 or 1:
    - returns 1 if value ≠ 0
    - returns 0 if value = 0 -/
def A_cleanup_bool (cleaned : Identifier) (value : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦cleaned ↦ if value = 0 then 0 else 1⟧

set_option maxHeartbeats 800000

lemma cleanup_bool_abs_of_concrete {s₀ s₉ : State} {cleaned value} :
  Spec (cleanup_bool_concrete_of_code.1 cleaned value) s₀ s₉ →
  Spec (A_cleanup_bool cleaned value) s₀ s₉ := by
  unfold cleanup_bool_concrete_of_code A_cleanup_bool
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMIszero', fromBool, List.head!, Bool.toUInt256] at hconcrete
  symm
  convert hconcrete using 2
  all_goals (by_cases hv : value = 0 <;> simp [hv, lookup_insert'])

end

end generated.L1Nullifier.L1Nullifier
