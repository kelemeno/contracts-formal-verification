import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_8324017772499216088_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    if iszero(split_expr_5) { var_result := add(var_result, 1) }

Yul's `if` fires on a nonzero guard and `iszero(v)` is nonzero exactly when
`v = 0`, so the increment happens precisely when `split_expr_5` is zero:

* `split_expr_5 = 0`  ⇒ `var_result` is incremented by one, nothing else moves.
* `split_expr_5 ≠ 0`  ⇒ no-op.

Self-contained: does not mention `if_8324017772499216088_concrete_of_code`.
-/
def A_if_8324017772499216088 (s₀ s₉ : State) : Prop :=
  ((s₀["split_expr_5"]!!) = 0 → s₉ = s₀⟦"var_result" ↦ (s₀["var_result"]!!) + 1⟧)
  ∧ ((s₀["split_expr_5"]!!) ≠ 0 → s₉ = s₀)

lemma if_8324017772499216088_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8324017772499216088_concrete_of_code s₀ s₉ →
  Spec A_if_8324017772499216088 s₀ s₉ := by
  unfold if_8324017772499216088_concrete_of_code A_if_8324017772499216088
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  refine ⟨?_, ?_⟩
  · intro hz
    rw [if_pos hz] at hc
    exact hc.symm
  · intro hnz
    rw [if_neg hnz] at hc
    exact hc.symm

end

end InteropHandler.Common
