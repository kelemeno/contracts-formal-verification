import Clear.ReasoningPrinciple

import specs.KeccakInjective
import specs.KeccakDistinct
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_update_fold_user

/-
  DISCHARGE LAYER (A6″) — the walk slot-stability hypothesis becomes
  arithmetic.

  Memory writes and keccak steps do not touch storage (`sload_mstore`,
  `sload_keccakOut`); the single `sstore` per walk level lands at an
  array-element slot `keccak(…) + j`, which never aliases a reserved low slot
  by the A6″ spread idealization (`keccak256_add_ne_lowSlot`).  Hence
  `updateWalk` preserves every low slot (`updateWalk_sload_low`) — the
  `hwalk_ss` hypothesis of the tree-builder closed forms is discharged for
  collision-free walks with small element indices.
-/

namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism Clear.KeccakInjective

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-- `mstore` does not touch storage. -/
lemma sload_mstore (σ : EVMState) (a v s : UInt256) :
    (σ.mstore a v).sload s = σ.sload s := rfl

/-- A successful `keccak256` step does not touch storage. -/
lemma keccak256_sload {σ σ' : EVMState} {p n r s : UInt256}
    (h : σ.keccak256 p n = some (r, σ')) : σ'.sload s = σ.sload s := by
  unfold EVMState.keccak256 at h
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some val =>
    simp only [hl] at h
    obtain ⟨-, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    rw [← h2]
  | none =>
    simp only [hl] at h
    cases hpart : σ.keccak_range.partition (fun x => x ∈ σ.used_range) with
    | mk used unused =>
      cases unused with
      | nil => simp only [hpart] at h
      | cons hd tl =>
        simp only [hpart] at h
        obtain ⟨-, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        rw [← h2]
        rfl

/-- A collision-free `keccakOut` step does not touch storage. -/
lemma sload_keccakOut_of_clean {σ : EVMState} {p n : UInt256} (s : UInt256)
    (h : (keccakOut σ p n).2.hash_collision = false) :
    ((keccakOut σ p n).2).sload s = σ.sload s := by
  have hs := keccakOut_some_of_clean h
  exact keccak256_sload (r := (keccakOut σ p n).1) (by rw [hs])

/-- A collision-free `arrOut` step does not touch storage. -/
lemma sload_arrOut_of_clean {σ : EVMState} {a : UInt256} (s : UInt256)
    (h : (arrOut σ a).2.hash_collision = false) :
    ((arrOut σ a).2).sload s = σ.sload s := by
  have := sload_keccakOut_of_clean (σ := σ.mstore 0 a) (p := 0) (n := 32) s h
  rw [show (arrOut σ a).2 = (keccakOut (σ.mstore 0 a) 0 32).2 from rfl, this,
      sload_mstore]

/-- A collision-free `accOut` step does not touch storage. -/
lemma sload_accOut_of_clean {σ : EVMState} {x y : UInt256} (s : UInt256)
    (h : (accOut σ x y).2.hash_collision = false) :
    ((accOut σ x y).2).sload s = σ.sload s := by
  have := sload_keccakOut_of_clean (σ := (σ.mstore 0 x).mstore 32 y)
    (p := 0) (n := 64) s h
  rw [show (accOut σ x y).2 = (keccakOut ((σ.mstore 0 x).mstore 32 y) 0 64).2 from rfl,
      this, sload_mstore, sload_mstore]

/-- The parent store of one walk level misses every reserved low slot (A6″):
the write lands at `keccak(levelArray) + j` with `j` small. -/
lemma nodeStore_sload_low
    {σ : EVMState} {base l j v s : UInt256}
    (hclean : (arrOut (arrOut σ base).2 ((arrOut σ base).1 + l)).2.hash_collision = false)
    (hcleanA : (arrOut σ base).2.hash_collision = false)
    (hj : j.val < lowSlotBound)
    (hs : s.val < lowSlotBound) :
    (nodeStore σ base l j v).sload s = σ.sload s := by
  unfold nodeStore
  have hksome := keccakOut_some_of_clean
    (σ := ((arrOut σ base).2.mstore 0 ((arrOut σ base).1 + l))) (p := 0) (n := 32)
    (by exact hclean)
  have hpair : ((arrOut σ base).2.mstore 0 ((arrOut σ base).1 + l)).keccak256 0 32
      = some ((arrOut (arrOut σ base).2 ((arrOut σ base).1 + l)).1,
              (arrOut (arrOut σ base).2 ((arrOut σ base).1 + l)).2) := by
    rw [hksome]
    rfl
  have hne : (arrOut (arrOut σ base).2 ((arrOut σ base).1 + l)).1 + j ≠ s :=
    keccak256_add_ne_lowSlot j s hpair hj hs
  rw [Clear.KeccakDistinct.sload_sstore_of_ne _ (Ne.symm hne)]
  rw [sload_arrOut_of_clean s hclean]
  rw [sload_arrOut_of_clean s hcleanA]

/-- Collision-flag monotonicity, backwards through `arrOut`. -/
private lemma arrOut_clean_backward {σ : EVMState} {a : UInt256}
    (h : (arrOut σ a).2.hash_collision = false) : σ.hash_collision = false := by
  have := keccakOut_clean_backward (σ := σ.mstore 0 a) (p := 0) (n := 32) h
  rwa [hash_collision_mstore] at this

/-- Collision-flag monotonicity, backwards through `accOut`. -/
private lemma accOut_clean_backward {σ : EVMState} {x y : UInt256}
    (h : (accOut σ x y).2.hash_collision = false) : σ.hash_collision = false := by
  have := keccakOut_clean_backward (σ := (σ.mstore 0 x).mstore 32 y) (p := 0) (n := 64) h
  rwa [hash_collision_mstore, hash_collision_mstore] at this

/-- The innermost hash flag of a step's node store (odd shape). -/
def oddFinClean (σ : EVMState) (base i idx cur : UInt256) : Prop :=
  (arrOut (arrOut (accOut (sibRead σ base i (idx - 1)).2
      (sibRead σ base i (idx - 1)).1 cur).2 base).2
    ((arrOut (accOut (sibRead σ base i (idx - 1)).2
      (sibRead σ base i (idx - 1)).1 cur).2 base).1 + (i + 1))).2.hash_collision = false

/-- **Odd step preserves low slots** (A6″ + storage frames). -/
lemma stepOdd_sload_low
    {σ : EVMState} {base i idx cur s : UInt256}
    (hs : s.val < lowSlotBound)
    (hj : (Fin.shiftRight idx 1).val < lowSlotBound)
    (hfin : oddFinClean σ base i idx cur) :
    ((stepOdd σ base i idx cur).2).sload s = σ.sload s := by
  unfold oddFinClean at hfin
  have h4 := arrOut_clean_backward hfin
  have h3 := arrOut_clean_backward h4
  have h2 := accOut_clean_backward h3
  have h1 := arrOut_clean_backward h2
  show (nodeStore (accOut (sibRead σ base i (idx - 1)).2
      (sibRead σ base i (idx - 1)).1 cur).2 base (i + 1) (Fin.shiftRight idx 1)
      (accOut (sibRead σ base i (idx - 1)).2 (sibRead σ base i (idx - 1)).1 cur).1).sload s
    = σ.sload s
  rw [nodeStore_sload_low hfin h4 hj hs]
  rw [sload_accOut_of_clean s h3]
  show ((arrOut (arrOut σ base).2 ((arrOut σ base).1 + i)).2).sload s = σ.sload s
  rw [sload_arrOut_of_clean s h2]
  rw [sload_arrOut_of_clean s h1]

/-- The innermost hash flag of a step's node store (even shape). -/
def evenFinClean (σ : EVMState) (base i idx cur : UInt256) : Prop :=
  (arrOut (arrOut (accOut (sibRead σ base i (idx + 1)).2 cur
      (sibRead σ base i (idx + 1)).1).2 base).2
    ((arrOut (accOut (sibRead σ base i (idx + 1)).2 cur
      (sibRead σ base i (idx + 1)).1).2 base).1 + (i + 1))).2.hash_collision = false

/-- **Even step preserves low slots**. -/
lemma stepEven_sload_low
    {σ : EVMState} {base i idx cur s : UInt256}
    (hs : s.val < lowSlotBound)
    (hj : (Fin.shiftRight idx 1).val < lowSlotBound)
    (hfin : evenFinClean σ base i idx cur) :
    ((stepEven σ base i idx cur).2).sload s = σ.sload s := by
  unfold evenFinClean at hfin
  have h4 := arrOut_clean_backward hfin
  have h3 := arrOut_clean_backward h4
  have h2 := accOut_clean_backward h3
  have h1 := arrOut_clean_backward h2
  show (nodeStore (accOut (sibRead σ base i (idx + 1)).2 cur
      (sibRead σ base i (idx + 1)).1).2 base (i + 1) (Fin.shiftRight idx 1)
      (accOut (sibRead σ base i (idx + 1)).2 cur (sibRead σ base i (idx + 1)).1).1).sload s
    = σ.sload s
  rw [nodeStore_sload_low hfin h4 hj hs]
  rw [sload_accOut_of_clean s h3]
  show ((arrOut (arrOut σ base).2 ((arrOut σ base).1 + i)).2).sload s = σ.sload s
  rw [sload_arrOut_of_clean s h2]
  rw [sload_arrOut_of_clean s h1]

/-- The innermost hash flag of a step's node store (edge shape). -/
def edgeFinClean (σ : EVMState) (ss base i idx cur : UInt256) : Prop :=
  (arrOut (arrOut (accOut (sideRead σ (ss + 3) i).2 cur
      (sideRead σ (ss + 3) i).1).2 base).2
    ((arrOut (accOut (sideRead σ (ss + 3) i).2 cur
      (sideRead σ (ss + 3) i).1).2 base).1 + (i + 1))).2.hash_collision = false

/-- **Edge step preserves low slots**. -/
lemma stepEdge_sload_low
    {σ : EVMState} {ss base i idx cur s : UInt256}
    (hs : s.val < lowSlotBound)
    (hj : (Fin.shiftRight idx 1).val < lowSlotBound)
    (hfin : edgeFinClean σ ss base i idx cur) :
    ((stepEdge σ ss base i idx cur).2).sload s = σ.sload s := by
  unfold edgeFinClean at hfin
  have h4 := arrOut_clean_backward hfin
  have h3 := arrOut_clean_backward h4
  have h2 := accOut_clean_backward h3
  have h1 := arrOut_clean_backward h2
  show (nodeStore (accOut (sideRead σ (ss + 3) i).2 cur
      (sideRead σ (ss + 3) i).1).2 base (i + 1) (Fin.shiftRight idx 1)
      (accOut (sideRead σ (ss + 3) i).2 cur (sideRead σ (ss + 3) i).1).1).sload s
    = σ.sload s
  rw [nodeStore_sload_low hfin h4 hj hs]
  rw [sload_accOut_of_clean s h3]
  show ((arrOut σ (ss + 3)).2).sload s = σ.sload s
  rw [sload_arrOut_of_clean s h2]

/-- Per-step discharge conditions: small write offset + innermost hash flag
clean, dispatched by parity/edge. -/
def StepLowOK (ss base : UInt256)
    (t : EVMState × UInt256 × UInt256 × UInt256 × UInt256) : Prop :=
  (Fin.shiftRight t.2.2.1 1).val < lowSlotBound ∧
  (if Fin.land t.2.2.1 1 = 0 then
    (if t.2.2.2.1 = t.2.2.1 then edgeFinClean t.1 ss base t.2.1 t.2.2.1 t.2.2.2.2
     else evenFinClean t.1 base t.2.1 t.2.2.1 t.2.2.2.2)
   else oddFinClean t.1 base t.2.1 t.2.2.1 t.2.2.2.2)

/-- **The dispatched step preserves low slots**. -/
lemma updateStep_sload_low
    {σ : EVMState} {ss base i idx maxN cur s : UInt256}
    (hs : s.val < lowSlotBound)
    (hok : StepLowOK ss base (σ, i, idx, maxN, cur)) :
    ((updateStep σ ss base i idx maxN cur).2).sload s = σ.sload s := by
  obtain ⟨hj, hflag⟩ := hok
  unfold updateStep
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge]
      rw [if_pos hpar, if_pos hedge] at hflag
      exact stepEdge_sload_low hs hj hflag
    · rw [if_pos hpar, if_neg hedge]
      rw [if_pos hpar, if_neg hedge] at hflag
      exact stepEven_sload_low hs hj hflag
  · rw [if_neg hpar]
    rw [if_neg hpar] at hflag
    exact stepOdd_sload_low hs hj hflag

/-- **THE WALK PRESERVES EVERY LOW SLOT** — the `hwalk_ss` hypothesis of the
tree-builder closed forms, discharged (A6″). -/
lemma updateWalk_sload_low :
    ∀ (kk : ℕ) {σ : EVMState} {ss base i idx maxN cur s : UInt256},
    s.val < lowSlotBound →
    (∀ j, j < kk → StepLowOK ss base (updateWalk ss base j σ i idx maxN cur)) →
    ((updateWalk ss base kk σ i idx maxN cur).1).sload s = σ.sload s := by
  intro kk
  induction kk with
  | zero =>
    intro σ ss base i idx maxN cur s _ _
    rfl
  | succ kk ih =>
    intro σ ss base i idx maxN cur s hs hok
    have h0 := hok 0 (by omega)
    simp only [updateWalk] at h0 ⊢
    rw [ih hs (by
      intro j hj
      have := hok (j+1) (by omega)
      simpa only [updateWalk] using this)]
    exact updateStep_sload_low hs h0

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
