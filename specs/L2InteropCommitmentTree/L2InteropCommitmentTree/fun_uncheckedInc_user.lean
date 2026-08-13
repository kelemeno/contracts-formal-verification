import Clear.ReasoningPrinciple
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_uncheckedInc_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **`fun_uncheckedInc(n) = n + 1`, with NO overflow check.**

This is Solidity's `unchecked { ++x }`, and it is what the tree uses to grow its LEVEL
count -- unlike the leaf index, which goes through the checked `increment_uint256`.  So
the level count wraps silently at `2^256 - 1` where the leaf index would revert.  That
is sound only because reaching it requires 2^256 level additions, but it is a real
asymmetry between the two counters and worth having stated. -/
def A_fun_uncheckedInc (var : Identifier) (var_number : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["var_number"],[var_number]⟧⟦"var" ↦ var_number + 1⟧
  s₉ = 🧟f🏪⟦s₀⟧⟦var ↦ f["var"]!!⟧

lemma fun_uncheckedInc_abs_of_concrete {s₀ s₉ : State} {var var_number} :
  Spec (fun_uncheckedInc_concrete_of_code.1 var var_number) s₀ s₉ →
  Spec (A_fun_uncheckedInc var var_number) s₀ s₉ := by
  unfold fun_uncheckedInc_concrete_of_code A_fun_uncheckedInc
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

lemma fun_uncheckedInc_isOk {var : Identifier} {var_number : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_fun_uncheckedInc var var_number s₀ s₉) : isOk s₉ := by
  subst h
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma fun_uncheckedInc_not_break {var : Identifier} {var_number : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_fun_uncheckedInc var var_number s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (fun_uncheckedInc_isOk hnf h)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
