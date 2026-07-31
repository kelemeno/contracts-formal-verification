import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_1042799038883876994_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/--
Abstract spec for the Yul block

    if iszero(expr_1) { expr_1 := iszero(expr_287_component) }

The chain-agnostic fallback of the executor authorization: if the exact-chain
check (`expr_1`) failed, accept iff the declared chainId
(`expr_287_component`) is `0`.

* If `expr_1 = 0`, the body runs and `expr_1` is rebound to
  `fromBool (expr_287_component = 0)` (1 when chain-agnostic, 0 otherwise);
  the EVM is untouched.
* If `expr_1 ≠ 0`, the block is a no-op: `s₉ = s₀`.
-/
def A_if_1042799038883876994 (s₀ s₉ : State) : Prop :=
  (s₀["expr_1"]!! = 0 →
      s₉ = s₀⟦"expr_1" ↦ fromBool (s₀["expr_287_component"]!! = 0)⟧)
  ∧ (s₀["expr_1"]!! ≠ 0 → s₉ = s₀)

lemma if_1042799038883876994_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1042799038883876994_concrete_of_code s₀ s₉ →
  Spec A_if_1042799038883876994 s₀ s₉ := by
  unfold if_1042799038883876994_concrete_of_code A_if_1042799038883876994
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  refine ⟨?_, ?_⟩
  · intro hz
    rw [if_pos hz] at hc
    rw [← hc]
    simp only [fromBool, Bool.toUInt256, decide_eq_true_eq]
  · intro hnz
    rw [if_neg hnz] at hc
    exact hc.symm

end

end InteropHandler.Common
