import Clear.ReasoningPrinciple
import specs.StateOk


import generated.AtomicFlowManager.AtomicFlowManager.cleanup_bool_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **`cleanup_bool(value) = iszero(iszero(value))`** — normalise a word to 0 or 1.

Solidity's `bool` is a word that must be exactly 0 or 1; a storage or calldata word that
happens to hold 2 would break `if`-dispatch elsewhere.  Double `iszero` maps every
non-zero value to 1 and 0 to 0 — see `cleanup_bool_is_zero_or_one`. -/
def A_cleanup_bool (cleaned : Identifier) (value : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["value"],[value]⟧
  let a := f⟦"split_expr_0" ↦ (decide (value = 0)).toUInt256⟧
  let b := a⟦"cleaned" ↦ (decide (a["split_expr_0"]!! = 0)).toUInt256⟧
  s₉ = 🧟b🏪⟦s₀⟧⟦cleaned ↦ b["cleaned"]!!⟧

lemma cleanup_bool_abs_of_concrete {s₀ s₉ : State} {cleaned value} :
  Spec (cleanup_bool_concrete_of_code.1 cleaned value) s₀ s₉ →
  Spec (A_cleanup_bool cleaned value) s₀ s₉ := by
  unfold cleanup_bool_concrete_of_code A_cleanup_bool
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

/-- **The normalisation is exactly 0-or-1.**  `iszero(iszero(v))` is `0` when `v = 0` and
`1` otherwise, for every word — so the result is a valid Solidity `bool` regardless of
what the input word held. -/
lemma cleanup_bool_is_zero_or_one (v : UInt256) :
    (decide ((decide (v = 0)).toUInt256 = 0)).toUInt256 = if v = 0 then 0 else 1 := by
  by_cases h : v = 0
  · simp [h]
  · simp [h]

lemma cleanup_bool_isOk {cleaned : Identifier} {value : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_cleanup_bool cleaned value s₀ s₉) : isOk s₉ := by
  subst h
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma cleanup_bool_not_break {cleaned : Identifier} {value : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_cleanup_bool cleaned value s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (cleanup_bool_isOk hnf h)

end

end generated.AtomicFlowManager.AtomicFlowManager
