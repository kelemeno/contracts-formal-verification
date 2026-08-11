import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_3587587773060279037_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    if gt(diff, x) {
      let split_expr_0 := shl(224, 1313373041)   -- Panic(uint256)
      mstore(0, split_expr_0)
      mstore(4, 17)                              -- 0x11, arithmetic overflow
      revert(0, 36)
    }

`checked_sub_uint256`'s underflow guard.  `diff := sub(x, y)` wraps exactly when
`diff > x`, and the block REVERTS in that case; when `diff ≤ x` it is a no-op.
So the helper returns a genuine difference rather than a wrapped one — the fact
every caller of `checked_sub_uint256` needs.

The no-op case is stated first because that is how the compiled form branches
(`if diff ≤ x then unchanged else revert-path`).

Self-contained: does not mention `if_3587587773060279037_concrete_of_code`.
-/
def A_if_3587587773060279037 (s₀ s₉ : State) : Prop :=
  (s₀["diff"]!! ≤ s₀["x"]!! → s₉ = s₀)
    ∧ (¬ (s₀["diff"]!! ≤ s₀["x"]!!) → s₉.evm.reverted = true)

lemma if_3587587773060279037_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3587587773060279037_concrete_of_code s₀ s₉ →
  Spec A_if_3587587773060279037 s₀ s₉ := by
  unfold if_3587587773060279037_concrete_of_code A_if_3587587773060279037
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  refine ⟨?_, ?_⟩
  · intro h
    rw [if_pos h] at hc
    exact hc.symm
  · intro h
    rw [if_neg h] at hc
    rw [← hc]
    rfl

end

end InteropHandler.Common
