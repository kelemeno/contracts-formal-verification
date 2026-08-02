import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_7798053233758968324_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    if gt(32, split_expr_35) { _11 := returndatasize() }

`gt` yields `fromBool (32 > split_expr_35)` and Yul's `if` fires on a nonzero guard, so
`_11` is set to the current `returndatasize()` exactly when `32 > split_expr_35` — the
standard clamp of a copy length to what the call actually returned:

* `32 > split_expr_35`  ⇒ `_11 := returndatasize()`, nothing else moves.
* otherwise    ⇒ no-op.

Self-contained: does not mention `if_7798053233758968324_concrete_of_code`.
-/
def A_if_7798053233758968324 (s₀ s₉ : State) : Prop :=
  ((32 : UInt256) > (s₀["split_expr_35"]!!) → s₉ = s₀⟦"_11" ↦ s₀.evm.returndatasize⟧)
  ∧ (¬ ((32 : UInt256) > (s₀["split_expr_35"]!!)) → s₉ = s₀)

lemma if_7798053233758968324_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7798053233758968324_concrete_of_code s₀ s₉ →
  Spec A_if_7798053233758968324 s₀ s₉ := by
  unfold if_7798053233758968324_concrete_of_code A_if_7798053233758968324
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  refine ⟨?_, ?_⟩
  · intro hgt
    rw [if_neg (not_le.mpr hgt)] at hc
    exact hc.symm
  · intro hngt
    rw [if_pos (not_lt.mp hngt)] at hc
    exact hc.symm

end

end InteropHandler.Common
