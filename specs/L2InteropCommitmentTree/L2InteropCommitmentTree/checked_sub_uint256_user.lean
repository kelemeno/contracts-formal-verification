import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakFuel
import specs.KeccakLowSlot
import specs.KeccakClean
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_1169358955168516216
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear Clear.StorageFrame Clear.KeccakLowSlot EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- `checked_sub_uint256(x) = x - 1`, the compiler's checked decrement.

The Yul is
```
    let split_expr_0 := not(0)      -- 2^256 - 1
    diff := add(x, split_expr_0)    -- x + (2^256-1)  =  x - 1  (mod 2^256)
    if gt(diff, x) { panic_error_0x11() }
```
so subtraction-by-one is done by WRAPPING ADDITION, and the underflow check is
the comparison `diff > x` — which is exactly `x = 0`, see
`checked_sub_underflow_iff` below.

The spec pins the frame: the two local assignments with their actual values, the
guard applied to that frame, and — the part that matters to a caller — that the
OUT parameter `diff` is bound to the guard's result and the caller's store is
restored (`🧟ss🏪⟦s₀⟧`). The guard's own behaviour is delegated to
`A_if_1169358955168516216`, which is closed and contentful: it either leaves the
state alone or runs `panic_error_0x11`. -/
def A_checked_sub_uint256 (diff : Identifier) (x : Literal) (s₀ s₉ : State) : Prop :=
  let s₁ := s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧
  let s₂ := s₁⟦"diff" ↦ s₁["x"]!! + (s₁["split_expr_0"]!!)⟧
  ∃ ss, Spec A_if_1169358955168516216 s₂ ss ∧ 🧟ss🏪⟦s₀⟧⟦diff ↦ ss["diff"]!!⟧ = s₉

lemma checked_sub_uint256_abs_of_concrete {s₀ s₉ : State} {diff x} :
  Spec (checked_sub_uint256_concrete_of_code.1 diff x) s₀ s₉ →
  Spec (A_checked_sub_uint256 diff x) s₀ s₉ := by
  intro h
  simpa [A_checked_sub_uint256] using h

/-- `lnot 0` is `2^256 - 1`. -/
lemma lnot_zero_val : (UInt256.lnot 0).val = UInt256.size - 1 := by rfl

/-- **The guard fires exactly on underflow.**  `add(x, not(0))` wraps to `x - 1`,
and the compiler's check `gt(diff, x)` — i.e. the negation of `diff ≤ x` — holds
precisely when `x = 0`.  So `checked_sub_uint256` reverts with panic `0x11` on
`x = 0` and on nothing else.

This is the mathematical content of the guard, separated from the state plumbing:
`A_if_1169358955168516216` branches on `s["diff"]!! ≤ s["x"]!!`, and this says what
that comparison means about the argument. -/
lemma checked_sub_underflow_iff (a : UInt256) :
    a + UInt256.lnot 0 ≤ a ↔ a ≠ 0 := by
  rw [Fin.le_def, Fin.val_add, lnot_zero_val]
  constructor
  · intro h hz
    subst hz
    simp only [Fin.val_zero, Nat.zero_add] at h
    have hlt : UInt256.size - 1 < UInt256.size := by
      unfold UInt256.size; omega
    rw [Nat.mod_eq_of_lt hlt] at h
    unfold UInt256.size at h
    omega
  · intro hne
    have hv : a.val ≠ 0 := fun hz => hne (Fin.ext (by simpa using hz))
    have hlt := a.isLt
    have key : a.val + (UInt256.size - 1) = (a.val - 1) + UInt256.size := by
      unfold UInt256.size at *; omega
    rw [key, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- **Output is `Ok`.**  Same chain as the index accessor: the guard's output is `Ok`
(a revert is an `Ok` state carrying the flag), and `revive`/`setStore`/`insert`
preserve that.  `¬ ❓ s₉` is required and propagates BACKWARDS to the guard's output
through those three constructors -- `Spec` is vacuous on out-of-fuel, so without it
the guard could hand back `OutOfFuel`. -/
lemma checked_sub_uint256_isOk {diff : Identifier} {x : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_checked_sub_uint256 diff x s₀ s₉) : isOk s₉ := by
  obtain ⟨ss, hif, heq⟩ := h
  subst heq
  have hss_nf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump']
    exact hoo
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_1169358955168516216_isOk
      (by simp [isOk_insert]; exact isOk_initcall_of_isOk hok) hss_nf
      (Spec_ok_unfold (P := L2InteropCommitmentTree.Common.A_if_1169358955168516216)
        (by simp [isOk_insert]; exact isOk_initcall_of_isOk hok) hss_nf hif)
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  rw [revive_of_ok hssok]
  exact hssok

lemma checked_sub_uint256_not_break {diff : Identifier} {x : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_checked_sub_uint256 diff x s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (checked_sub_uint256_isOk hok hnf h)


/-- **FRAME.**  Only `diff` moves. -/
lemma checked_sub_uint256_frame {diff : Identifier} {x : Literal} {v : Identifier}
    {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hv : v ≠ diff)
    (h : A_checked_sub_uint256 diff x s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  have hrev : isOk (🧟 ss) := by
    apply Clear.isOk_reviveJump_of_not_isOutOfFuel
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  rw [lookup_insert_of_ne hv, Clear.lookup_setStore hrev hok]


/-- **STORAGE FRAME.**  Guarded subtraction writes no storage on either branch. -/
lemma checked_sub_uint256_sload {diff : Identifier} {x q : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉) (h : A_checked_sub_uint256 diff x s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨ss, hif, heq⟩ := h
  subst heq
  have hs2ok : isOk ((s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)⟦"diff" ↦
      (s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["x"]!! +
      ((s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["split_expr_0"]!!)⟧) :=
    isOk_insert.mpr (isOk_insert.mpr (isOk_initcall_of_isOk hok))
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_1169358955168516216_isOk hs2ok hssnf
      (Spec_ok_unfold hs2ok hssnf hif)
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hssok,
    L2InteropCommitmentTree.Common.if_1169358955168516216_sload hs2ok hssnf
      (Spec_ok_unfold hs2ok hssnf hif)]
  simp only [evm_insert]
  rw [Clear.evm_initcall hok]


/-- **CONFIG FRAME.**  Guarded subtraction keeps the keccak window on both branches. -/
lemma checked_sub_uint256_config {diff : Identifier} {x : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : RangeInWindow s₀.evm) (hC : CachedInWindow s₀.evm)
    (h : A_checked_sub_uint256 diff x s₀ s₉) :
    RangeInWindow s₉.evm ∧ CachedInWindow s₉.evm := by
  obtain ⟨ss, hif, heq⟩ := h
  subst heq
  have hs2ok : isOk ((s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)⟦"diff" ↦
      (s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["x"]!! +
      ((s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["split_expr_0"]!!)⟧) :=
    isOk_insert.mpr (isOk_insert.mpr (isOk_initcall_of_isOk hok))
  have hs2e : ((s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)⟦"diff" ↦
      (s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["x"]!! +
      ((s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["split_expr_0"]!!)⟧).evm = s₀.evm := by
    simp only [evm_insert]; exact Clear.evm_initcall hok
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_1169358955168516216_isOk hs2ok hssnf
      (Spec_ok_unfold hs2ok hssnf hif)
  have hcfg := L2InteropCommitmentTree.Common.if_1169358955168516216_config hs2ok hssnf
    (by rw [hs2e]; exact hR) (by rw [hs2e]; exact hC) (Spec_ok_unfold hs2ok hssnf hif)
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hssok]
  exact hcfg

/-- **FUEL FRAME.**  The checked subtraction spends no pool on either branch. -/
lemma checked_sub_uint256_fuel {diff : Identifier} {x : Literal} {k : ℕ} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hf : Clear.KeccakFuel.Fuel s₀.evm k)
    (h : A_checked_sub_uint256 diff x s₀ s₉) : Clear.KeccakFuel.Fuel s₉.evm k := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf0 : isOk (s₀☎️⟦["x"],[x]⟧) := isOk_initcall_of_isOk hok
  have hs1ok : isOk ((s₀☎️⟦["x"],[x]⟧)⟦"split_expr_0" ↦ UInt256.lnot 0⟧) :=
    isOk_insert.mpr hf0
  have hs2ok : isOk (((s₀☎️⟦["x"],[x]⟧)⟦"split_expr_0" ↦ UInt256.lnot 0⟧)⟦"diff" ↦
      ((s₀☎️⟦["x"],[x]⟧)⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["x"]!!
        + (((s₀☎️⟦["x"],[x]⟧)⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["split_expr_0"]!!)⟧) :=
    isOk_insert.mpr hs1ok
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [← heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump']
    exact hoo
  have hsok : isOk ss :=
    L2InteropCommitmentTree.Common.if_1169358955168516216_isOk hs2ok hssnf
      (Spec_ok_unfold hs2ok hssnf hg)
  have hfss : Clear.KeccakFuel.Fuel ss.evm k := by
    refine L2InteropCommitmentTree.Common.if_1169358955168516216_fuel hs2ok hssnf ?_
      (Spec_ok_unfold hs2ok hssnf hg)
    simp only [evm_insert]
    rw [Clear.evm_initcall hok]
    exact hf
  rw [← heq]
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hsok]
  exact hfss

/-- **CLEAN FLAG.**  The checked subtraction never hashes, on either branch. -/
lemma checked_sub_uint256_clean {diff : Identifier} {x : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_checked_sub_uint256 diff x s₀ s₉) :
    Clear.KeccakClean.Clean s₉.evm ↔ Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨ss, hif, heq⟩ := h
  subst heq
  have hs2ok : isOk ((s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)⟦"diff" ↦
      (s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["x"]!! +
      ((s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["split_expr_0"]!!)⟧) :=
    isOk_insert.mpr (isOk_insert.mpr (isOk_initcall_of_isOk hok))
  have hs2e : ((s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)⟦"diff" ↦
      (s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["x"]!! +
      ((s₀☎️⟦["x"],[x]⟧⟦"split_expr_0" ↦ UInt256.lnot 0⟧)["split_expr_0"]!!)⟧).evm = s₀.evm := by
    simp only [evm_insert]; exact Clear.evm_initcall hok
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_1169358955168516216_isOk hs2ok hssnf
      (Spec_ok_unfold hs2ok hssnf hif)
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hssok,
    L2InteropCommitmentTree.Common.if_1169358955168516216_clean hs2ok hssnf
      (Spec_ok_unfold hs2ok hssnf hif), hs2e]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
