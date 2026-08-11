import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_4527419366897270229_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    if iszero(split_expr_5) {
      let split_expr_6 := shl(225, 1157535291)   -- error selector
      mstore(0, split_expr_6)
      mstore(4, sum)
      mstore(36, cleaned)
      revert(0, 68)
    }

A guard with a two-word error payload: when `split_expr_5` is zero the block
REVERTS, otherwise it is a no-op.  Same shape as the inclusion gate
(`if_7459957530221088163`), with more `mstore`s before the `revert` — which do
not change the spec, since a reverting branch is characterised by the flag.

Self-contained: does not mention `if_4527419366897270229_concrete_of_code`.
-/
def A_if_4527419366897270229 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_5"]!! = 0 → s₉.evm.reverted = true)
    ∧ (s₀["split_expr_5"]!! ≠ 0 → s₉ = s₀)

lemma if_4527419366897270229_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4527419366897270229_concrete_of_code s₀ s₉ →
  Spec A_if_4527419366897270229 s₀ s₉ := by
  unfold if_4527419366897270229_concrete_of_code A_if_4527419366897270229
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  refine ⟨?_, ?_⟩
  · intro hz
    rw [if_pos hz] at hc
    rw [← hc]
    rfl
  · intro hnz
    rw [if_neg hnz] at hc
    exact hc.symm

end

end InteropHandler.Common
