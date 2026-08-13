import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_8835011984658778953_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **The pointer bound check**: `if sgt(addr, split_expr_7) { revert(0, 0) }`.

A calldata pointer is rejected when it runs past the bound, compared SIGNED — the
same discipline as the tail-offset check (block_5731116343986243113): a pointer
that has wrapped reads as negative and fails, rather than sailing past the bound
as a huge unsigned value.

Reverts inline, so the branch is the whole content.  Note the generator states the
condition as `sgt … = false` on the surviving branch rather than negating it. -/
def A_if_8835011984658778953 (s₀ s₉ : State) : Prop :=
  (UInt256.sgt (s₀["addr"]!!) (s₀["split_expr_7"]!!) = false → s₉ = s₀) ∧
  (¬ (UInt256.sgt (s₀["addr"]!!) (s₀["split_expr_7"]!!) = false) → s₉ = s₀🇪⟦Clear.EVMState.evm_revert s₀.evm 0 0⟧)

lemma if_8835011984658778953_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8835011984658778953_concrete_of_code s₀ s₉ →
  Spec A_if_8835011984658778953 s₀ s₉ := by
  unfold if_8835011984658778953_concrete_of_code A_if_8835011984658778953
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  dsimp only at hc
  constructor
  · intro hg
    rw [if_pos hg] at hc
    exact hc.symm
  · intro hg
    rw [if_neg hg] at hc
    exact hc.symm

/-- Output is `Ok` on both branches: a revert is an `Ok` state carrying the flag. -/
lemma if_8835011984658778953_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_8835011984658778953 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨h₁, h₂⟩ := h
    by_cases hg : UInt256.sgt ((Ok evm store)["addr"]!!) ((Ok evm store)["split_expr_7"]!!) = false
    · rw [h₁ hg]; simp [isOk]
    · rw [h₂ hg]; simp [isOk, State.setEvm]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_8835011984658778953_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_8835011984658778953 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_8835011984658778953_isOk hok h)

end

end AtomicFlowManager.Common
