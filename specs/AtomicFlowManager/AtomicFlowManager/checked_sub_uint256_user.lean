import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1169358955168516216
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x11

import generated.AtomicFlowManager.AtomicFlowManager.checked_sub_uint256_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

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

end

end generated.AtomicFlowManager.AtomicFlowManager
