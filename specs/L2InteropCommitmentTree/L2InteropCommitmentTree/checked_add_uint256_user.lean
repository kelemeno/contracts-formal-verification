import Clear.ReasoningPrinciple
import specs.KeccakClean
import specs.StorageFrame
import specs.KeccakFuel
import specs.KeccakLowSlot
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_7624433659449274775
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear Clear.StorageFrame Clear.KeccakLowSlot EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **`checked_add_uint256(x) = x + 1`** — the compiler's checked increment, and the
mirror of AtomicFlowManager's `checked_sub_uint256` decrement.

```
    sum := add(x, 1)
    if gt(x, sum) { panic_error_0x11() }
```

The guard fires exactly when `x + 1` wraps, i.e. at `2^256 - 1` -- see
`checked_add_overflow_iff`.  (Note this name means something DIFFERENT in other
contracts; solc reuses these names for genuinely different functions, which is why
scripts/port-spec.sh refuses to port without comparing the Yul.) -/
def A_checked_add_uint256 (sum : Identifier) (x : Literal) (s₀ s₉ : State) : Prop :=
  let s₁ := s₀☎️⟦["x"],[x]⟧
  let s₂ := s₁⟦"sum" ↦ s₁["x"]!! + 1⟧
  ∃ ss, Spec L2InteropCommitmentTree.Common.A_if_7624433659449274775 s₂ ss ∧
    🧟ss🏪⟦s₀⟧⟦sum ↦ ss["sum"]!!⟧ = s₉

lemma checked_add_uint256_abs_of_concrete {s₀ s₉ : State} {sum x} :
  Spec (checked_add_uint256_concrete_of_code.1 sum x) s₀ s₉ →
  Spec (A_checked_add_uint256 sum x) s₀ s₉ := by
  unfold checked_add_uint256_concrete_of_code A_checked_add_uint256
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc

/-- **The guard fires exactly on overflow.**  `x + 1` exceeds `x` unless it wraps,
which happens only at `2^256 - 1`. -/
lemma checked_add_overflow_iff (a : UInt256) :
    a ≤ a + 1 ↔ a.val ≠ UInt256.size - 1 := by
  rw [Fin.le_def, Fin.val_add]
  constructor
  · intro h hv
    have h1 : (1 : UInt256).val = 1 := by unfold UInt256.size; rfl
    rw [h1, hv] at h
    -- at the top value the successor wraps to 0, so the guard's comparison fails
    have hz : (UInt256.size - 1 + 1) % UInt256.size = 0 := by
      have he : UInt256.size - 1 + 1 = UInt256.size := by unfold UInt256.size; omega
      rw [he, Nat.mod_self]
    rw [hz] at h
    unfold UInt256.size at h
    omega
  · intro hne
    have hlt := a.isLt
    have h1 : (1 : UInt256).val = 1 := by unfold UInt256.size; rfl
    rw [h1, Nat.mod_eq_of_lt (by unfold UInt256.size at *; omega)]
    omega

lemma checked_add_uint256_isOk {sum : Identifier} {x : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_checked_add_uint256 sum x s₀ s₉) : isOk s₉ := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma checked_add_uint256_not_break {sum : Identifier} {x : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_checked_add_uint256 sum x s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (checked_add_uint256_isOk hnf h)


/-- **FRAME.**  Only `sum` changes; every other variable reads through to the caller.
See `Clear.lookup_setStore` for why, and `checked_div_uint256_frame` for what it is for. -/
lemma checked_add_uint256_frame {sum : Identifier} {x : Literal} {v : Identifier}
    {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hv : v ≠ sum)
    (h : A_checked_add_uint256 sum x s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  have hrev : isOk (🧟 ss) := by
    apply Clear.isOk_reviveJump_of_not_isOutOfFuel
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  rw [lookup_insert_of_ne hv, Clear.lookup_setStore hrev hok]


/-- **STORAGE FRAME.**  Guarded addition writes no storage on either branch. -/
lemma checked_add_uint256_sload {sum : Identifier} {x q : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉) (h : A_checked_add_uint256 sum x s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨ss, hif, heq⟩ := h
  subst heq
  have hs2ok : isOk ((s₀☎️⟦["x"],[x]⟧)⟦"sum" ↦ (s₀☎️⟦["x"],[x]⟧)["x"]!! + 1⟧) :=
    isOk_insert.mpr (isOk_initcall_of_isOk hok)
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_7624433659449274775_isOk hs2ok hssnf
      (Spec_ok_unfold hs2ok hssnf hif)
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hssok,
    L2InteropCommitmentTree.Common.if_7624433659449274775_sload hs2ok hssnf
      (Spec_ok_unfold hs2ok hssnf hif)]
  simp only [evm_insert]
  rw [Clear.evm_initcall hok]


/-- **CONFIG FRAME.**  Guarded addition keeps the keccak window on both branches. -/
lemma checked_add_uint256_config {sum : Identifier} {x : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : RangeInWindow s₀.evm) (hC : CachedInWindow s₀.evm)
    (h : A_checked_add_uint256 sum x s₀ s₉) :
    RangeInWindow s₉.evm ∧ CachedInWindow s₉.evm := by
  obtain ⟨ss, hif, heq⟩ := h
  subst heq
  have hs2ok : isOk ((s₀☎️⟦["x"],[x]⟧)⟦"sum" ↦ (s₀☎️⟦["x"],[x]⟧)["x"]!! + 1⟧) :=
    isOk_insert.mpr (isOk_initcall_of_isOk hok)
  have hs2e : ((s₀☎️⟦["x"],[x]⟧)⟦"sum" ↦ (s₀☎️⟦["x"],[x]⟧)["x"]!! + 1⟧).evm = s₀.evm := by
    simp only [evm_insert]; exact Clear.evm_initcall hok
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_7624433659449274775_isOk hs2ok hssnf
      (Spec_ok_unfold hs2ok hssnf hif)
  have hcfg := L2InteropCommitmentTree.Common.if_7624433659449274775_config hs2ok hssnf
    (by rw [hs2e]; exact hR) (by rw [hs2e]; exact hC) (Spec_ok_unfold hs2ok hssnf hif)
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hssok]
  exact hcfg

/-- **FUEL FRAME.**  The checked addition spends no pool on either branch: it adds, compares
and returns, and its overflow panic writes memory and reverts.

With `checked_div_uint256_evm` (which passes the whole machine state through) this completes
the arithmetic helpers, so a hash budget survives the three of them that sit between the
fold body's two accessor calls. -/
lemma checked_add_uint256_fuel {sum : Identifier} {x : Literal} {k : ℕ} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hf : Clear.KeccakFuel.Fuel s₀.evm k)
    (h : A_checked_add_uint256 sum x s₀ s₉) : Clear.KeccakFuel.Fuel s₉.evm k := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf0 : isOk (s₀☎️⟦["x"],[x]⟧) := isOk_initcall_of_isOk hok
  have hs2ok : isOk ((s₀☎️⟦["x"],[x]⟧)⟦"sum" ↦ (s₀☎️⟦["x"],[x]⟧)["x"]!! + 1⟧) :=
    isOk_insert.mpr hf0
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [← heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump']
    exact hoo
  have hsok : isOk ss :=
    L2InteropCommitmentTree.Common.if_7624433659449274775_isOk hs2ok hssnf
      (Spec_ok_unfold hs2ok hssnf hg)
  have hfss : Clear.KeccakFuel.Fuel ss.evm k := by
    refine L2InteropCommitmentTree.Common.if_7624433659449274775_fuel hs2ok hssnf ?_
      (Spec_ok_unfold hs2ok hssnf hg)
    simp only [evm_insert]
    rw [Clear.evm_initcall hok]
    exact hf
  rw [← heq]
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hsok]
  exact hfss

/-- **CLEAN FLAG.**  An addition and an overflow check: no hash on either branch. -/
lemma checked_add_uint256_clean {sum : Identifier} {x : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_checked_add_uint256 sum x s₀ s₉) :
    Clear.KeccakClean.Clean s₉.evm ↔ Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨ss, hif, heq⟩ := h
  subst heq
  have hs2ok : isOk ((s₀☎️⟦["x"],[x]⟧)⟦"sum" ↦ (s₀☎️⟦["x"],[x]⟧)["x"]!! + 1⟧) :=
    isOk_insert.mpr (isOk_initcall_of_isOk hok)
  have hs2e : ((s₀☎️⟦["x"],[x]⟧)⟦"sum" ↦ (s₀☎️⟦["x"],[x]⟧)["x"]!! + 1⟧).evm = s₀.evm := by
    simp only [evm_insert]; exact Clear.evm_initcall hok
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_7624433659449274775_isOk hs2ok hssnf
      (Spec_ok_unfold hs2ok hssnf hif)
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hssok,
    L2InteropCommitmentTree.Common.if_7624433659449274775_clean hs2ok hssnf
      (Spec_ok_unfold hs2ok hssnf hif), hs2e]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
