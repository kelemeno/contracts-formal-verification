import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_5874076488583661551_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    if iszero(split_expr_27) { revert(0, 0) }

* Guard `split_expr_27` zero  ⇒ the block REVERTS: the result is the initial state with
  its EVM replaced by `evm_revert evm 0 0`, so `s₉.evm.reverted = true`.
* Guard `split_expr_27` nonzero ⇒ the block is a no-op: `s₉ = s₀`.

Self-contained: does not mention `if_5874076488583661551_concrete_of_code`, so the bridge
lemma below carries real content rather than degenerating to
`concrete → concrete`.
-/
def A_if_5874076488583661551 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_27"]!! = 0 →
      s₉ = s₀🇪⟦s₀.evm.evm_revert 0 0⟧ ∧ s₉.evm.reverted = true)
  ∧ (s₀["split_expr_27"]!! ≠ 0 → s₉ = s₀)

lemma if_5874076488583661551_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5874076488583661551_concrete_of_code s₀ s₉ →
  Spec A_if_5874076488583661551 s₀ s₉ := by
  unfold if_5874076488583661551_concrete_of_code A_if_5874076488583661551
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
