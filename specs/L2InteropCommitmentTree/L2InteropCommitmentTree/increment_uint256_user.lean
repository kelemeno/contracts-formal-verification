import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2896693009130145472
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.increment_uint256_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **`increment_uint256(value) = value + 1`, checked BEFORE the add.**

```
    let split_expr_0 := not(0)
    if eq(value, split_expr_0) { panic_error_0x11() }
    ret := add(value, 1)
```

The tree uses this for its LEAF INDEX (`nextIndex`), where an overflow reverts -- in
contrast to `fun_uncheckedInc`, used for the level count, which has no check at all. -/
def A_increment_uint256 (ret : Identifier) (value : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["value"],[value]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧
  ∃ ss, Spec L2InteropCommitmentTree.Common.A_if_2896693009130145472 f ss ∧
    (let r := ss⟦"ret" ↦ ss["value"]!! + 1⟧
     s₉ = 🧟r🏪⟦s₀⟧⟦ret ↦ r["ret"]!!⟧)

lemma increment_uint256_abs_of_concrete {s₀ s₉ : State} {ret value} :
  Spec (increment_uint256_concrete_of_code.1 ret value) s₀ s₉ →
  Spec (A_increment_uint256 ret value) s₀ s₉ := by
  unfold increment_uint256_concrete_of_code A_increment_uint256
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨ss, hg, heq⟩ := hc
  exact ⟨ss, hg, heq.symm⟩

lemma increment_uint256_isOk {ret : Identifier} {value : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_increment_uint256 ret value s₀ s₉) : isOk s₉ := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma increment_uint256_not_break {ret : Identifier} {value : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_increment_uint256 ret value s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (increment_uint256_isOk hnf h)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
