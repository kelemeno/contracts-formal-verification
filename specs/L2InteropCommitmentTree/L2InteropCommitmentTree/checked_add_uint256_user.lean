import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_7624433659449274775
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

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

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
