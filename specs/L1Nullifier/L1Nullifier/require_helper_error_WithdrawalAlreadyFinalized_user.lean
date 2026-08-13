import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L1Nullifier.L1Nullifier.Common.if_9006375582650777893

import generated.L1Nullifier.L1Nullifier.require_helper_error_WithdrawalAlreadyFinalized_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

/-- **`require(condition, WithdrawalAlreadyFinalized())`.**

A pure assertion -- no output parameters -- wrapping `if_9006375582650777893`.  A caller
that returns from this call knows `condition` was nonzero; a zero condition reverts with
the named error.

In the replay path the condition is `iszero(isWithdrawalFinalized[chain][addr])` after
`cleanup_bool`, so passing this call means the withdrawal was NOT already finalized. -/
def A_require_helper_error_WithdrawalAlreadyFinalized (condition : Literal) (s₀ s₉ : State) : Prop :=
  ∃ ss, Spec L1Nullifier.Common.A_if_9006375582650777893
      (s₀☎️⟦["condition"],[condition]⟧) ss ∧
    s₉ = 🧟ss🏪⟦s₀⟧

lemma require_helper_error_WithdrawalAlreadyFinalized_abs_of_concrete {s₀ s₉ : State} {condition} :
  Spec (require_helper_error_WithdrawalAlreadyFinalized_concrete_of_code.1 condition) s₀ s₉ →
  Spec (A_require_helper_error_WithdrawalAlreadyFinalized condition) s₀ s₉ := by
  unfold require_helper_error_WithdrawalAlreadyFinalized_concrete_of_code A_require_helper_error_WithdrawalAlreadyFinalized
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨ss, hg, heq⟩ := hc
  exact ⟨ss, hg, heq.symm⟩

lemma require_helper_error_WithdrawalAlreadyFinalized_isOk {condition : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_require_helper_error_WithdrawalAlreadyFinalized condition s₀ s₉) : isOk s₉ := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma require_helper_error_WithdrawalAlreadyFinalized_not_break {condition : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_require_helper_error_WithdrawalAlreadyFinalized condition s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (require_helper_error_WithdrawalAlreadyFinalized_isOk hnf h)

end

end generated.L1Nullifier.L1Nullifier
