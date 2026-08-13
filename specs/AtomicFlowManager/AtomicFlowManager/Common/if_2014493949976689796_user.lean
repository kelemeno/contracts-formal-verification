import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2014493949976689796_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **The enum range guard**: `if iszero(lt(value, 4)) { … revert }`.

The revert payload is Solidity's BUILT-IN `Panic(uint256)` — selector
`shl(224, 1313373041) = 0x4e487b71` — with code `33` (`0x21`), which is
"enum conversion out of range".  That is why `scripts/error-selector.sh` finds no
match for it: built-in panics are not declared with `error` anywhere in the
source, unlike `ManagerBundleHashesNotSorted()`.

`LegState` has four values, so a stored byte outside `0..3` cannot be read back as
a `LegState` — the contract panics instead of silently treating it as one of them. -/
def A_if_2014493949976689796 (s₀ s₉ : State) : Prop :=
  let sel := Fin.shiftLeft 1313373041 224
  let sm := Clear.State.multifill ["split_expr_1"] [sel] s₀
  let s₁ := Clear.State.multifill ["split_expr_1"] [sel]
      s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (sm["split_expr_1"]!!)⟧
  let s₂ := s₁🇪⟦Clear.EVMState.mstore s₁.evm 4 33⟧
  (s₀["split_expr_0"]!! = 0 → s₉ = s₂🇪⟦Clear.EVMState.evm_revert s₂.evm 0 36⟧) ∧
  (s₀["split_expr_0"]!! ≠ 0 → s₉ = s₀)

lemma if_2014493949976689796_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2014493949976689796_concrete_of_code s₀ s₉ →
  Spec A_if_2014493949976689796 s₀ s₉ := by
  unfold if_2014493949976689796_concrete_of_code A_if_2014493949976689796
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

/-- Output is `Ok` on both branches: the panic branch is stores + revert, and a
revert is an `Ok` state carrying the flag. -/
lemma if_2014493949976689796_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_2014493949976689796 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨h₁, h₂⟩ := h
    by_cases hg : (Ok evm store)["split_expr_0"]!! = 0
    · rw [h₁ hg]
      simp only [isOk_setEvm]
      exact isOk_multifill (by simp [isOk])
    · rw [h₂ hg]; simp [isOk]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_2014493949976689796_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_2014493949976689796 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_2014493949976689796_isOk hok h)

end

end AtomicFlowManager.Common
