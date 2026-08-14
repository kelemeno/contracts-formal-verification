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

/-- **THE UNCHECKED INCREMENT RETURNS `n + 1` -- WITH NO GUARD AT ALL.**

Worth stating beside `increment_uint256_val`, because the contract uses the two for
different counters and the asymmetry is real: the LEAF count goes through the checked
increment, which panics at `2^256 - 1`; the LEVEL count goes through this one, which does
not check anything.  Here that is sound only because the level count is bounded by the
tree's height, not because the function protects it.

There is no overflow hypothesis because there is no overflow BRANCH -- at `2^256 - 1` this
wraps to `0` and says so.  Any argument that it does not is an argument about the caller. -/
lemma fun_uncheckedInc_val {var : Identifier} {var_number : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (h : A_fun_uncheckedInc var var_number s₀ s₉) :
    s₉[var]!! = var_number + 1 := by
  subst h
  have hf0 : isOk (s₀☎️⟦["var_number"],[var_number]⟧) := isOk_initcall_of_isOk hok
  have hfok : isOk ((s₀☎️⟦["var_number"],[var_number]⟧)⟦"var" ↦ var_number + 1⟧) :=
    isOk_insert.mpr hf0
  rw [lookup_insert' (isOk_setStore_of_isOk (by rw [revive_of_ok hfok]; exact hfok)),
    lookup_insert' hf0]

/-- **STORAGE FRAME.**  The unchecked increment writes no storage at all -- it reads a
parameter, adds one, and returns.  Needed to carry the tree's LEAF count across the level
counter's increment. -/
lemma fun_uncheckedInc_sload {var : Identifier} {var_number : Literal} {q : UInt256}
    {s₀ s₉ : State} (hok : isOk s₀) (h : A_fun_uncheckedInc var var_number s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  subst h
  have hf0 : isOk (s₀☎️⟦["var_number"],[var_number]⟧) := isOk_initcall_of_isOk hok
  have hfok : isOk ((s₀☎️⟦["var_number"],[var_number]⟧)⟦"var" ↦ var_number + 1⟧) :=
    isOk_insert.mpr hf0
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hfok]
  simp only [evm_insert]
  rw [Clear.evm_initcall hok]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
