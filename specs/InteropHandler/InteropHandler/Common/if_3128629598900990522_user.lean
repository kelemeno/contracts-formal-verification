import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_3128629598900990522_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/--
Abstract spec for the Yul block

    if iszero(split_expr_3) { revert(0, 0) }

* If the guard variable `split_expr_3` is zero, the block reverts: the
  resulting state is the initial state with its EVM replaced by
  `evm_revert evm 0 0` (which sets the `reverted` flag and clears
  `return_data`); in particular `s₉.evm.reverted = true`.
* If `split_expr_3` is nonzero, the block is a no-op: `s₉ = s₀`.
-/
def A_if_3128629598900990522 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_3"]!! = 0 →
      s₉ = s₀🇪⟦s₀.evm.evm_revert 0 0⟧ ∧ s₉.evm.reverted = true)
  ∧ (s₀["split_expr_3"]!! ≠ 0 → s₉ = s₀)

lemma if_3128629598900990522_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3128629598900990522_concrete_of_code s₀ s₉ →
  Spec A_if_3128629598900990522 s₀ s₉ := by
  unfold if_3128629598900990522_concrete_of_code A_if_3128629598900990522
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

end InteropHandler.Common
