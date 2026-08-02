import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_3535069651717937529_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    if gt(size, split_expr_52) { _13 := returndatasize() }

`gt` yields `fromBool (size > split_expr_52)` and Yul's `if` fires on a nonzero guard, so
`_13` is set to the current `returndatasize()` exactly when `size > split_expr_52` — the
standard clamp of a copy length to what the call actually returned:

* `size > split_expr_52`  ⇒ `_13 := returndatasize()`, nothing else moves.
* otherwise    ⇒ no-op.

Self-contained: does not mention `if_3535069651717937529_concrete_of_code`.
-/
def A_if_3535069651717937529 (s₀ s₉ : State) : Prop :=
  ((s₀["size"]!!) > (s₀["split_expr_52"]!!) → s₉ = s₀⟦"_13" ↦ s₀.evm.returndatasize⟧)
  ∧ (¬ ((s₀["size"]!!) > (s₀["split_expr_52"]!!)) → s₉ = s₀)

lemma if_3535069651717937529_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3535069651717937529_concrete_of_code s₀ s₉ →
  Spec A_if_3535069651717937529 s₀ s₉ := by
  unfold if_3535069651717937529_concrete_of_code A_if_3535069651717937529
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
