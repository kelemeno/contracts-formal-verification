import Clear.ReasoningPrinciple


import generated.L1Bridgehub.L1Bridgehub.Common.if_3489657594510812776_gen


namespace L1Bridgehub.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

def finalize_allocation_overflow (s : State) : Prop :=
  s["split_expr_3"]!! ≠ 0 ∨ s["split_expr_4"]!! ≠ 0

def A_if_3489657594510812776 (s₀ s₉ : State) : Prop :=
  ¬ finalize_allocation_overflow s₀ → s₉ = s₀

lemma if_3489657594510812776_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3489657594510812776_concrete_of_code s₀ s₉ →
  Spec A_if_3489657594510812776 s₀ s₉ := by
  unfold if_3489657594510812776_concrete_of_code A_if_3489657594510812776
    finalize_allocation_overflow
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hconcrete hsafe
  simp only [not_or, not_not] at hsafe
  obtain ⟨h3, h4⟩ := hsafe
  simp only [EVMOr', fromBool] at hconcrete
  simp only [h3, h4] at hconcrete
  simp [Bool.toUInt256, UInt256.size] at hconcrete
  simpa using hconcrete.symm

end

end L1Bridgehub.Common
