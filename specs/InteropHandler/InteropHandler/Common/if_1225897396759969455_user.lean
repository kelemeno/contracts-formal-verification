import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_1225897396759969455_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    if gt(offset_4, 18446744073709551615) { revert(0, 0) }

`gt` yields `fromBool (offset_4 > 18446744073709551615)` and Yul's `if` fires on a NONZERO guard, so
the block reverts exactly when `offset_4 > 18446744073709551615`:

* `offset_4 > 18446744073709551615`  ⇒ REVERT: EVM replaced by `evm_revert evm 0 0`, hence
  `s₉.evm.reverted = true`.
* otherwise    ⇒ no-op: `s₉ = s₀`.

Self-contained: does not mention `if_1225897396759969455_concrete_of_code`.
-/
def A_if_1225897396759969455 (s₀ s₉ : State) : Prop :=
  (s₀["offset_4"]!! > (18446744073709551615 : UInt256) →
      s₉ = s₀🇪⟦s₀.evm.evm_revert 0 0⟧ ∧ s₉.evm.reverted = true)
  ∧ (¬ (s₀["offset_4"]!! > (18446744073709551615 : UInt256)) → s₉ = s₀)

lemma if_1225897396759969455_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1225897396759969455_concrete_of_code s₀ s₉ →
  Spec A_if_1225897396759969455 s₀ s₉ := by
  unfold if_1225897396759969455_concrete_of_code A_if_1225897396759969455
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
