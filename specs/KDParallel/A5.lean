import Clear.EVMState
import specs.KeccakDeterminism

/-!
# Frame-equality reflexivity / symmetry / transport (KDParallel A5)

Corollaries of the frame-conditioned accessor preimage equality
`accInterval_eq`. `accInterval_eq` takes a junk-window frame
`∀ i, 64 ≤ i.val → i.val ≤ 94 → lookup i σ₁.mem = lookup i σ₂.mem` and yields
`accInterval σ₁ = accInterval σ₂`. This file records the equivalence-relation
shape of that fact:

* `accInterval_eq_symm`: feeding the symmetric frame flips the equality.
* `accInterval_junk_frame`: a single `accOut` step preserves the junk window
  (`accOut_junk_window`), so its post-state has the same `accInterval` as its
  input.
* `accInterval_eq_trans`: composing two frame equalities, plus the 2-step
  junk-frame specialization.

All axiom-free (they only compose existing frame lemmas).
-/

namespace Clear.KeccakDeterminism

open Clear EVMState

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-- **Symmetry** of the frame-conditioned interval equality: a frame hypothesis
in the `σ₁ = σ₂` direction yields the interval equality in the `σ₂ = σ₁`
direction (apply `accInterval_eq` to the symmetric frame). -/
theorem accInterval_eq_symm
    {σ₁ σ₂ : EVMState} {key base : UInt256}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory = Finmap.lookup i σ₂.machine_state.memory) :
    accInterval σ₂ key base = accInterval σ₁ key base :=
  accInterval_eq (fun i h1 h2 => (hframe i h1 h2).symm)

/-- **Single-step junk-frame transport**: one accessor step preserves the junk
window `[64, 95)` (`accOut_junk_window`), so its post-state produces the same
accessor preimage interval as its input state, for any `(key, base)`. -/
theorem accInterval_junk_frame
    {σ₁ σ₂ : EVMState} {k b key base : UInt256}
    (hσ₂ : σ₂ = (accOut σ₁ k b).2) :
    accInterval σ₂ key base = accInterval σ₁ key base := by
  subst hσ₂
  exact accInterval_eq
    (fun i h1 _ => accOut_junk_window (σ := σ₁) (key := k) (base := b) h1)

/-- **Transitivity** of interval equality: two chained frame equalities compose
(a trivial `Eq.trans`, recorded for symmetry with the relation shape). -/
theorem accInterval_eq_trans
    {σ₁ σ₂ σ₃ : EVMState} {key base : UInt256}
    (h₁ : accInterval σ₁ key base = accInterval σ₂ key base)
    (h₂ : accInterval σ₂ key base = accInterval σ₃ key base) :
    accInterval σ₁ key base = accInterval σ₃ key base :=
  h₁.trans h₂

/-- **Two-step junk-frame transport**: the junk window survives two consecutive
accessor steps (`accOut_junk_window₂`), so the post-state of a 2-step chain
produces the same accessor preimage interval as the original input state. -/
theorem accInterval_junk_frame₂
    {σ₁ σ₂ : EVMState} {k₁ b₁ k₂ b₂ key base : UInt256}
    (hσ₂ : σ₂ = (accOut (accOut σ₁ k₁ b₁).2 k₂ b₂).2) :
    accInterval σ₂ key base = accInterval σ₁ key base := by
  subst hσ₂
  exact accInterval_eq
    (fun i h1 _ => accOut_junk_window₂ (σ := σ₁) (k₁ := k₁) (b₁ := b₁)
      (k₂ := k₂) (b₂ := b₂) h1)

end Clear.KeccakDeterminism
