import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_8272552103943281487_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Reading a variable is unaffected by replacing the EVM. -/
private lemma lookup_setEvm {s : State} {e : EVM} {v : Identifier} :
    (s🇪⟦e⟧)[v]!! = s[v]!! := by
  unfold State.setEvm State.lookup!; rcases s <;> rfl

/--
Abstract spec for the Yul block

      if iszero(split_expr_1)
      {
      var_value := result_1
      var_result := add(var_result, 8)
      }

Yul's `if` fires on a NONZERO guard and `iszero(v)` is nonzero exactly when
`v = 0`, so the body runs precisely when `split_expr_1` is zero.  On that branch every
bound variable is given in CLOSED FORM over the entry state and the whole
memory/storage effect is the composed chain in source order; otherwise the block
is a no-op.

Self-contained: does not mention `if_8272552103943281487_concrete_of_code`.
-/
def A_if_8272552103943281487 (s₀ s₉ : State) : Prop :=
  ((s₀["split_expr_1"]!!) = 0 → s₉ = ((s₀⟦"var_value" ↦ (s₀["result_1"]!!)⟧)⟦"var_result" ↦ (s₀["var_result"]!!) + (8 : UInt256)⟧))
  ∧ (¬ ((s₀["split_expr_1"]!!) = 0) → s₉ = s₀)

lemma if_8272552103943281487_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8272552103943281487_concrete_of_code s₀ s₉ →
  Spec A_if_8272552103943281487 s₀ s₉ := by
  unfold if_8272552103943281487_concrete_of_code A_if_8272552103943281487
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  repeat rw [multifill_cons] at hc
  repeat rw [multifill_nil] at hc
  repeat first
    | rw [lookup_setEvm] at hc
    | rw [lookup_insert' (by aesop)] at hc
    | rw [lookup_insert] at hc
    | rw [lookup_insert_of_ne (by decide)] at hc
  refine ⟨?_, ?_⟩
  · intro hz
    rw [if_pos hz] at hc
    exact hc.symm
  · intro hnz
    rw [if_neg hnz] at hc
    exact hc.symm

end

end InteropHandler.Common
