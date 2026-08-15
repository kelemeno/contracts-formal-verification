import Clear.ReasoningPrinciple
import specs.KeccakLowSlot
import specs.KeccakClean
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

/-- **THE CHECKED INCREMENT RETURNS `value + 1`.**

solc's `increment_uint256` compares against `not(0)` FIRST and panics on equality, so off
that path it simply adds one.  The tree's leaf counter goes through this, which is why
"one push, one leaf" needs it: the increment is checked, so the count cannot silently wrap.

The `2^256 - 1` case is excluded by hypothesis rather than by reachability -- a real tree
never gets there, but that is an argument about the caller, not about this function. -/
lemma increment_uint256_val {ret : Identifier} {value : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hno : value ≠ UInt256.lnot 0)
    (h : A_increment_uint256 ret value s₀ s₉) : s₉[ret]!! = value + 1 := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf0 : isOk (s₀☎️⟦["value"],[value]⟧) := isOk_initcall_of_isOk hok
  have hfok : isOk ((s₀☎️⟦["value"],[value]⟧)⟦"split_expr_0" ↦ UInt256.lnot 0⟧) :=
    isOk_insert.mpr hf0
  have hvalue : ((s₀☎️⟦["value"],[value]⟧)⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["value"]!!
      = value := by
    rw [lookup_insert_of_ne (by decide)]
    exact Clear.lookup_initcall_one hok
  have hsplit : ((s₀☎️⟦["value"],[value]⟧)⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["split_expr_0"]!!
      = UInt256.lnot 0 := lookup_insert' hf0
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump']
    exact hoo
  have hss : ss = (s₀☎️⟦["value"],[value]⟧)⟦"split_expr_0" ↦ UInt256.lnot 0⟧ :=
    L2InteropCommitmentTree.Common.if_2896693009130145472_id_of_ne
      (by rw [hvalue, hsplit]; exact hno) (Spec_ok_unfold hfok hssnf hg)
  subst heq
  rw [hss]
  have hrok : isOk (((s₀☎️⟦["value"],[value]⟧)⟦"split_expr_0" ↦ UInt256.lnot 0⟧)⟦"ret" ↦
      ((s₀☎️⟦["value"],[value]⟧)⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["value"]!! + 1⟧) :=
    isOk_insert.mpr hfok
  rw [lookup_insert' (isOk_setStore_of_isOk (by rw [revive_of_ok hrok]; exact hrok)),
    lookup_insert' hfok, hvalue]

/-- **STORAGE FRAME.**  The checked increment writes no storage on either branch -- it
compares, adds and returns, and its panic writes memory and reverts.  UNCONDITIONAL, so the
tree's leaf count can be carried across the counter's own increment without splitting on
whether the overflow guard fired. -/
lemma increment_uint256_sload {ret : Identifier} {value : Literal} {q : UInt256}
    {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_increment_uint256 ret value s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf0 : isOk (s₀☎️⟦["value"],[value]⟧) := isOk_initcall_of_isOk hok
  have hfok : isOk ((s₀☎️⟦["value"],[value]⟧)⟦"split_expr_0" ↦ UInt256.lnot 0⟧) :=
    isOk_insert.mpr hf0
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump']
    exact hoo
  have hsok : isOk ss :=
    L2InteropCommitmentTree.Common.if_2896693009130145472_isOk hfok hssnf
      (Spec_ok_unfold hfok hssnf hg)
  have hguard := L2InteropCommitmentTree.Common.if_2896693009130145472_sload (q := q)
    hfok hssnf (Spec_ok_unfold hfok hssnf hg)
  subst heq
  have hrok : isOk (ss⟦"ret" ↦ ss["value"]!! + 1⟧) := isOk_insert.mpr hsok
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hrok]
  simp only [evm_insert]
  rw [hguard]
  simp only [evm_insert]
  exact Clear.evm_initcall hok ▸ rfl

/-- **FRAME.**  Only `ret` moves: the overflow guard restores the caller's bindings. -/
lemma increment_uint256_frame {ret : Identifier} {value : Literal} {v : Identifier}
    {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hv : v ≠ ret)
    (h : A_increment_uint256 ret value s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  have hrev : isOk (🧟 (ss⟦"ret" ↦ ss["value"]!! + 1⟧)) := by
    apply Clear.isOk_reviveJump_of_not_isOutOfFuel
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  rw [lookup_insert_of_ne hv, Clear.lookup_setStore hrev hok]

/-- The state the overflow guard sees: the argument bound and the sentinel loaded. -/
private def incG (value : Literal) (s₀ : State) : State :=
  s₀☎️⟦["value"],[value]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧

private lemma incG_isOk {value : Literal} {s₀ : State} (hok : isOk s₀) :
    isOk (incG value s₀) := isOk_insert.mpr (isOk_initcall_of_isOk hok)

private lemma incG_evm {value : Literal} {s₀ : State} (hok : isOk s₀) :
    (incG value s₀).evm = s₀.evm := by
  simp only [incG, evm_insert]; exact Clear.evm_initcall hok

/-- **KECCAK WINDOW.**  An increment and an overflow check: no hashing, no storage. -/
lemma increment_uint256_config {ret : Identifier} {value : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_increment_uint256 ret value s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨ss, hg, heq⟩ := h
  have hgok := incG_isOk (value := value) hok
  have hge := incG_evm (value := value) hok
  have hssnf : ¬ ❓ ss := by
    intro hoo; apply hnf; rw [heq]
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have hga := Spec_ok_unfold hgok hssnf hg
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_2896693009130145472_isOk hgok hssnf hga
  obtain ⟨hRs, hCs⟩ := L2InteropCommitmentTree.Common.if_2896693009130145472_config hgok hssnf
    (by rw [hge]; exact hR) (by rw [hge]; exact hC) hga
  rw [heq, evm_insert, evm_setStore,
    Clear.evm_reviveJump_of_isOk (isOk_insert.mpr hssok), evm_insert]
  exact ⟨hRs, hCs⟩

/-- **CLEAN FLAG.**  Same reason: nothing here hashes. -/
lemma increment_uint256_clean {ret : Identifier} {value : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_increment_uint256 ret value s₀ s₉) :
    Clear.KeccakClean.Clean s₉.evm ↔ Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨ss, hg, heq⟩ := h
  have hgok := incG_isOk (value := value) hok
  have hge := incG_evm (value := value) hok
  have hssnf : ¬ ❓ ss := by
    intro hoo; apply hnf; rw [heq]
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have hga := Spec_ok_unfold hgok hssnf hg
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_2896693009130145472_isOk hgok hssnf hga
  rw [heq, evm_insert, evm_setStore,
    Clear.evm_reviveJump_of_isOk (isOk_insert.mpr hssok), evm_insert,
    L2InteropCommitmentTree.Common.if_2896693009130145472_clean hgok hssnf hga, hge]

/-- **ACCOUNT FRAME.**  The increment writes no storage, so the account map survives --
which is what lets a caller carry an account witness across it and then write. -/
lemma increment_uint256_account {ret : Identifier} {value : Literal} {addr : Address}
    {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_increment_uint256 ret value s₀ s₉) :
    Clear.EVMState.lookupAccount s₉.evm addr = Clear.EVMState.lookupAccount s₀.evm addr := by
  obtain ⟨ss, hg, heq⟩ := h
  have hgok := incG_isOk (value := value) hok
  have hge := incG_evm (value := value) hok
  have hssnf : ¬ ❓ ss := by
    intro hoo; apply hnf; rw [heq]
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have hga := Spec_ok_unfold hgok hssnf hg
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_2896693009130145472_isOk hgok hssnf hga
  rw [heq, evm_insert, evm_setStore,
    Clear.evm_reviveJump_of_isOk (isOk_insert.mpr hssok), evm_insert,
    L2InteropCommitmentTree.Common.if_2896693009130145472_account hgok hssnf hga, hge]

/-- **EXECUTION ENVIRONMENT FRAME.**  Carried alongside `_account`: an account witness is
stated at `code_owner`, so a caller needs both halves to move one across the increment. -/
lemma increment_uint256_env {ret : Identifier} {value : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_increment_uint256 ret value s₀ s₉) :
    s₉.evm.execution_env = s₀.evm.execution_env := by
  obtain ⟨ss, hg, heq⟩ := h
  have hgok := incG_isOk (value := value) hok
  have hge := incG_evm (value := value) hok
  have hssnf : ¬ ❓ ss := by
    intro hoo; apply hnf; rw [heq]
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have hga := Spec_ok_unfold hgok hssnf hg
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_2896693009130145472_isOk hgok hssnf hga
  rw [heq, evm_insert, evm_setStore,
    Clear.evm_reviveJump_of_isOk (isOk_insert.mpr hssok), evm_insert,
    L2InteropCommitmentTree.Common.if_2896693009130145472_env hgok hssnf hga, hge]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
