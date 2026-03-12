import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.fun_isContract_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- fun_isContract returns 1 if the account has code (extcodesize > 0), 0 otherwise. -/
def A_fun_isContract (var : Identifier) (var_account : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦var ↦ fromBool (s₀.evm.extCodeSize var_account ≠ 0)⟧

set_option maxHeartbeats 800000

lemma fun_isContract_abs_of_concrete {s₀ s₉ : State} {var var_account} :
  Spec (fun_isContract_concrete_of_code.1 var var_account) s₀ s₉ →
  Spec (A_fun_isContract var var_account) s₀ s₉ := by
  unfold fun_isContract_concrete_of_code A_fun_isContract
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMExtcodesize', EVMIszero'] at hconcrete
  symm
  by_cases h : evm.extCodeSize var_account = 0 <;> simp [fromBool, h] at *
  · exact hconcrete
  · exact hconcrete

end

end generated.L1Nullifier.L1Nullifier
