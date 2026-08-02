import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_2252518414917795087_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    if slt(split_expr_17, 96) { revert(0, 0) }

`slt` yields `fromBool (UInt256.slt split_expr_17 96)` (SIGNED less-than) and Yul's `if` fires on a
NONZERO guard, so the block reverts exactly when the signed comparison holds:

* `= true`  ⇒ REVERT: EVM replaced by `evm_revert evm 0 0`, hence
  `s₉.evm.reverted = true`.
* `= false` ⇒ no-op: `s₉ = s₀`.

Self-contained: does not mention `if_2252518414917795087_concrete_of_code`.
-/
def A_if_2252518414917795087 (s₀ s₉ : State) : Prop :=
  (UInt256.slt (s₀["split_expr_17"]!!) (96 : UInt256) = true →
      s₉ = s₀🇪⟦s₀.evm.evm_revert 0 0⟧ ∧ s₉.evm.reverted = true)
  ∧ (UInt256.slt (s₀["split_expr_17"]!!) (96 : UInt256) = false → s₉ = s₀)

lemma if_2252518414917795087_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2252518414917795087_concrete_of_code s₀ s₉ →
  Spec A_if_2252518414917795087 s₀ s₉ := by
  unfold if_2252518414917795087_concrete_of_code A_if_2252518414917795087
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  refine ⟨?_, ?_⟩
  · intro hs
    rw [if_neg (by simp [hs])] at hc
    refine ⟨hc.symm, ?_⟩
    rw [← hc]
    rfl
  · intro hns
    rw [if_pos hns] at hc
    exact hc.symm

end

end InteropHandler.Common
