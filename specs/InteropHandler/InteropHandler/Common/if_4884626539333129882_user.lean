import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_4884626539333129882_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    if gt(srcEnd, end_clear_sanitised_hrafn) { revert(0, 0) }

`gt` yields `fromBool (srcEnd > end_clear_sanitised_hrafn)` and Yul's `if` fires on a NONZERO guard, so
the block reverts exactly when `srcEnd > end_clear_sanitised_hrafn`:

* `srcEnd > end_clear_sanitised_hrafn`  ⇒ REVERT: EVM replaced by `evm_revert evm 0 0`, hence
  `s₉.evm.reverted = true`.
* otherwise    ⇒ no-op: `s₉ = s₀`.

Self-contained: does not mention `if_4884626539333129882_concrete_of_code`.
-/
def A_if_4884626539333129882 (s₀ s₉ : State) : Prop :=
  (s₀["srcEnd"]!! > s₀["end_clear_sanitised_hrafn"]!! →
      s₉ = s₀🇪⟦s₀.evm.evm_revert 0 0⟧ ∧ s₉.evm.reverted = true)
  ∧ (¬ (s₀["srcEnd"]!! > s₀["end_clear_sanitised_hrafn"]!!) → s₉ = s₀)

lemma if_4884626539333129882_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4884626539333129882_concrete_of_code s₀ s₉ →
  Spec A_if_4884626539333129882 s₀ s₉ := by
  unfold if_4884626539333129882_concrete_of_code A_if_4884626539333129882
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  refine ⟨?_, ?_⟩
  · intro hgt
    rw [if_neg (not_le.mpr hgt)] at hc
    refine ⟨hc.symm, ?_⟩
    rw [← hc]
    rfl
  · intro hngt
    rw [if_pos (not_lt.mp hngt)] at hc
    exact hc.symm

end

end InteropHandler.Common
