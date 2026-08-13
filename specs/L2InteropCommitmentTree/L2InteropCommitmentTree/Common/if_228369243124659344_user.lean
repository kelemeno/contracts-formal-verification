import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_228369243124659344_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **The offset-must-be-zero check**: `if offset { … revert }`.

Reverts INLINE with Solidity's built-in `Panic(uint256)` (`0x4e487b71`) carrying code
`0` -- the generic assertion failure, not one of the named codes.  A `bytes32` fills its
word, so a non-zero byte offset into one is a compiler invariant violation rather than a
user error, which is why the payload carries no diagnostic. -/
def A_if_228369243124659344 (s₀ s₉ : State) : Prop :=
  let sel := Fin.shiftLeft 1313373041 224
  let sm := Clear.State.multifill ["split_expr_2"] [sel] s₀
  let m1 := Clear.State.multifill ["split_expr_2"] [sel]
    s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (sm["split_expr_2"]!!)⟧
  let m2 := m1🇪⟦Clear.EVMState.mstore m1.evm 4 0⟧
  (s₀["offset"]!! = 0 → s₉ = s₀) ∧
  (s₀["offset"]!! ≠ 0 → s₉ = m2🇪⟦Clear.EVMState.evm_revert m2.evm 0 36⟧)

lemma if_228369243124659344_abs_of_concrete {s₀ s₉ : State} :
  Spec if_228369243124659344_concrete_of_code s₀ s₉ →
  Spec A_if_228369243124659344 s₀ s₉ := by
  unfold if_228369243124659344_concrete_of_code A_if_228369243124659344
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

lemma if_228369243124659344_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_228369243124659344 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨h₁, h₂⟩ := h
    by_cases hg : (Ok evm store)["offset"]!! = 0
    · rw [h₁ hg]; simp [isOk]
    · rw [h₂ hg]
      simp only [isOk_setEvm]
      exact isOk_multifill (by simp [isOk])
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_228369243124659344_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_228369243124659344 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_228369243124659344_isOk hok h)

end

end L2InteropCommitmentTree.Common
