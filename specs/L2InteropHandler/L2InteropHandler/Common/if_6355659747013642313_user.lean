import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.if_6355659747013642313_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_6355659747013642313 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_1"]!! = 0 →
      s₉ = s₀🇪⟦s₀.evm.evm_revert 0 0⟧ ∧ s₉.evm.reverted = true)
  ∧ (s₀["split_expr_1"]!! ≠ 0 → s₉ = s₀)

lemma if_6355659747013642313_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6355659747013642313_concrete_of_code s₀ s₉ →
  Spec A_if_6355659747013642313 s₀ s₉ := by
  unfold if_6355659747013642313_concrete_of_code A_if_6355659747013642313
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  refine ⟨?_, ?_⟩
  · intro hz
    rw [if_pos hz] at hc
    refine ⟨hc.symm, ?_⟩
    rw [← hc]
    rfl
  · intro hnz
    rw [if_neg hnz] at hc
    exact hc.symm

end

end L2InteropHandler.Common
