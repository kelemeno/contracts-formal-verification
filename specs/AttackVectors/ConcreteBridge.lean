import specs.IMTAbstract
import specs.AttackVectors.NoTheft
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_fidelity_user

/-
  THE CONCRETE-TO-ABSTRACT BRIDGE for the L2InteropCommitmentTree insert path.

  `AttackVectors.NoTheft` proves the security guarantees for any abstract
  `Evolution` / `GuardedEvolution` from genesis.  Its header lists, as
  out-of-scope obligation (i), that the abstract layer does NOT by itself show
  the deployed bytecode performs such steps.

  This file discharges that obligation at the level of the LEAF SET.  The
  concrete side already provides the per-step result

      generated.…L2InteropCommitmentTree.leafSetOf_evolution_step

  which shows that the insert path's storage-write sequence takes
  `leafSetOf σ` to `imtInsert (leafSetOf σ) W₀ v` with `W₀` in the current set
  and `v` strictly inside `W₀`'s window — exactly the insert disjunct of
  `IMTAbstract.Evolution`.  What was missing is the composition: lifting that
  per-step fact to a whole history and handing it to the no-theft capstone.

  ## What is proved here

  * `concreteHistory_isEvolution` — a state history whose every step is a no-op
    (on the leaf set) or a guarded concrete insert induces an
    `IMTAbstract.Evolution` on `fun n => leafSetOf (σ n)`.
  * `imt_no_theft` — consequently, a concrete history from the genesis leaf set,
    with monotone settlement timestamps, satisfies every clause of
    `AttackVectors.NoTheft.no_theft` for each nonzero commit value: exactly one
    outcome at each deadline-pinned snapshot, no double redemption, permanence
    of delivery, and a unique entry step.

  ## Trusted base — read this before quoting the result

  The theorems in THIS file are axiom-clean (`propext`, `Quot.sound`,
  `Classical.choice` only): they take the per-step fact as a HYPOTHESIS.

  Discharging that hypothesis with `leafSetOf_evolution_step` enlarges the
  trusted base by four deliberate cryptographic idealizations from
  `specs/KeccakInjective.lean`, confirmed via `#print axioms`:

      Clear.KeccakInjective.keccak256_inj
      Clear.KeccakInjective.keccak256_slot_sep
      Clear.KeccakInjective.keccak256_ne_lowSlot
      Clear.KeccakInjective.keccak256_add_ne_lowSlot

  So the honest end-to-end claim is: **modulo keccak collision-resistance and
  slot separation, the deployed insert path cannot be used to redeem a leg
  twice, to refund a delivered leg, or to deliver one twice.**

  ## Still out of scope

  * The leaf set is the abstraction; ROOT binding (that a published 32-byte root
    pins that leaf set) is separate — `MerkleSpec` M-D plus
    `AttackVectors.RootForgery`, and it rests on node-hash pair-injectivity as a
    hypothesis.
  * The no-op disjunct is a hypothesis about the OTHER entry points: this file
    does not enumerate the contract's remaining functions to prove none of them
    mutates the leaf set outside the insert path.
  * Genesis is a hypothesis, discharged in practice by the one-time-guarded
    `setup`; see `AttackVectors.ResetAndZero` for why that guard is load-bearing.
  * GOVERNANCE remains excepted by construction.
-/

namespace AttackVectors.ConcreteBridge

open Clear IMTAbstract
open generated.L2InteropCommitmentTree.L2InteropCommitmentTree

/-- A concrete state history performs, at every step, either no change to the
represented leaf set or one window-guarded insert.  This is the per-step shape
that `leafSetOf_evolution_step` establishes for the contract's insert path. -/
def ConcreteLeafHistory (σ : ℕ → EVMState) : Prop :=
  ∀ n, leafSetOf (σ (n+1)) = leafSetOf (σ n)
    ∨ ∃ W₀ v, W₀ ∈ leafSetOf (σ n) ∧ W₀.key < v
        ∧ (W₀.nextKey = 0 ∨ v < W₀.nextKey)
        ∧ leafSetOf (σ (n+1)) = imtInsert (leafSetOf (σ n)) W₀ v

/-- **THE CONCRETE HISTORY IS AN ABSTRACT EVOLUTION.**  Lifting the per-step
insert fact to a whole run: the represented leaf sets form an
`IMTAbstract.Evolution`, so every analytic security theorem applies to them. -/
theorem concreteHistory_isEvolution {σ : ℕ → EVMState}
    (h : ConcreteLeafHistory σ) :
    Evolution (fun n => leafSetOf (σ n)) := by
  intro n
  rcases h n with heq | ⟨W₀, v, hW₀, hlow, hwin, heq⟩
  · exact Or.inl heq
  · exact Or.inr ⟨W₀, v, hW₀, hlow, hwin, heq⟩

/-- **NO THEFT, FOR THE DEPLOYED INSERT PATH.**  A concrete history from the
genesis leaf set, with monotone settlement timestamps, satisfies every clause of
the abstract no-theft capstone for each nonzero commit value `v`:

1. exactly one outcome (delivered XOR reclaimable) at every deadline-pinned
   snapshot;
2. no double redemption across any pair of snapshots;
3. delivery is permanent;
4. a delivered leg has an entry step;
5. that entry step is unique.

See the file header for the trusted base that `leafSetOf_evolution_step`
introduces when it is used to discharge `ConcreteLeafHistory`. -/
theorem imt_no_theft {σ : ℕ → EVMState} {t : ℕ → UInt256} {D v : UInt256}
    (hhist : ConcreteLeafHistory σ)
    (hgen : leafSetOf (σ 0) = ({⟨0, 0⟩} : Finset AbsLeaf))
    (htmono : Monotone t) (hv0 : v ≠ 0) :
    (∀ j : ℕ, D < t (j + 1) →
        (NoTheft.Delivered (fun n => leafSetOf (σ n)) v j
          ∨ NoTheft.Reclaimable (fun n => leafSetOf (σ n)) v j)
        ∧ ¬ (NoTheft.Delivered (fun n => leafSetOf (σ n)) v j
          ∧ NoTheft.Reclaimable (fun n => leafSetOf (σ n)) v j))
    ∧ (∀ i j : ℕ, t i ≤ D → NoTheft.Delivered (fun n => leafSetOf (σ n)) v i →
          D < t (j + 1) → ¬ NoTheft.Reclaimable (fun n => leafSetOf (σ n)) v j)
    ∧ (∀ i j : ℕ, NoTheft.Delivered (fun n => leafSetOf (σ n)) v i → i ≤ j →
          NoTheft.Delivered (fun n => leafSetOf (σ n)) v j)
    ∧ (∀ n : ℕ, NoTheft.Delivered (fun n => leafSetOf (σ n)) v n →
          ∃ m, m < n ∧ NoTheft.EntersAt (fun n => leafSetOf (σ n)) v m)
    ∧ (∀ m₁ m₂ : ℕ, NoTheft.EntersAt (fun n => leafSetOf (σ n)) v m₁ →
          NoTheft.EntersAt (fun n => leafSetOf (σ n)) v m₂ → m₁ = m₂) := by
  -- A `ConcreteLeafHistory` is in particular a `GuardedEvolution`: the strict
  -- window it supplies is stronger than the weak loop-exit window, and the
  -- dedup gate follows because `v` lies strictly inside `W₀`'s window while the
  -- state is sound.
  have hevo : Evolution (fun n => leafSetOf (σ n)) := concreteHistory_isEvolution hhist
  have h0 : SoundState (leafSetOf (σ 0)) := by rw [hgen]; exact genesis_soundState
  have hv0' : v ∉ keys (leafSetOf (σ 0)) := by
    rw [hgen]
    intro hmem
    obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_singleton] at hL
    rw [hL] at hLkey
    exact hv0 hLkey.symm
  have hzero : (0 : UInt256) ∈ keys (leafSetOf (σ 0)) := by
    rw [hgen]; exact genesis_zero_mem
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    constructor
    · by_cases hd : v ∈ keys (leafSetOf (σ j))
      · exact Or.inl hd
      · exact Or.inr (reclaim_witness_available hevo h0 hzero hv0 hd)
    · rintro ⟨hd, hr⟩
      exact present_not_reclaimable (evolution_sound hevo h0 j).1 hd hr
  · intro i j hti hdel hpin hrec
    obtain ⟨W, hW, hlow, hwin⟩ := hrec
    exact delivered_and_reclaimed_impossible hevo h0.1 h0.2.1 htmono hti hdel hpin hW hlow hwin
  · intro i j hdel hij
    exact evolution_keys_mono hevo hij hdel
  · intro n hdel
    obtain ⟨m, hmn, habs, hstep⟩ := evolution_key_origin hevo n hdel hv0'
    exact ⟨m, hmn, habs, by rw [hstep]; exact Finset.mem_insert_self _ _⟩
  · intro m₁ m₂ h1 h2
    exact evolution_key_origin_unique hevo h1 h2

/-! ## Contract-level vocabulary

`imt_no_theft` above is stated through `NoTheft.Delivered` / `NoTheft.Reclaimable`
applied to `fun n => leafSetOf (σ n)`, which is precise but reads as abstract
set membership.  These name the same two conditions as facts about ONE deployed
contract state, so the capstone can be read without unfolding the history
plumbing. -/

/-- The leg with commit value `v` HAS BEEN DELIVERED in state `s`: its leaf is in
the tree the contract's storage represents. -/
def bundleDelivered (s : EVMState) (v : UInt256) : Prop :=
  v ∈ keys (leafSetOf s)

/-- A REFUND WITNESS for `v` exists in state `s`: some tree leaf's linked-list
window straddles `v`, which is what the reclaim gate demands as proof that `v`
was never inserted. -/
def refundWitnessExists (s : EVMState) (v : UInt256) : Prop :=
  ∃ W ∈ leafSetOf s, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **NO THEFT, IN CONTRACT TERMS.**  The same content as `imt_no_theft`, stated
over single deployed states rather than the abstract history:

1. at every deadline-pinned snapshot each nonzero leg is either delivered or
   refundable, and never both;
2. an on-time delivered leg admits no refund witness at any deadline-pinned
   snapshot;
3. delivery is permanent.

Proved by `exact`-ing `imt_no_theft`: `bundleDelivered` and `refundWitnessExists`
are definitionally the abstract predicates, so this is the same proposition in
readable clothing.  The trusted base is unchanged — see the file header. -/
theorem imt_no_theft_in_contract_terms
    {σ : ℕ → EVMState} {t : ℕ → UInt256} {D v : UInt256}
    (hhist : ConcreteLeafHistory σ)
    (hgen : leafSetOf (σ 0) = ({⟨0, 0⟩} : Finset AbsLeaf))
    (htmono : Monotone t) (hv0 : v ≠ 0) :
    (∀ j : ℕ, D < t (j + 1) →
        (bundleDelivered (σ j) v ∨ refundWitnessExists (σ j) v)
        ∧ ¬ (bundleDelivered (σ j) v ∧ refundWitnessExists (σ j) v))
    ∧ (∀ i j : ℕ, t i ≤ D → bundleDelivered (σ i) v → D < t (j + 1) →
          ¬ refundWitnessExists (σ j) v)
    ∧ (∀ i j : ℕ, bundleDelivered (σ i) v → i ≤ j → bundleDelivered (σ j) v) :=
  by
  obtain ⟨h1, h2, h3, _, _⟩ := imt_no_theft (D := D) hhist hgen htmono hv0
  exact ⟨h1, h2, h3⟩

end AttackVectors.ConcreteBridge
