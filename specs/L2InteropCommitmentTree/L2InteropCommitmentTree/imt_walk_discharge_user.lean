import Clear.ReasoningPrinciple

import specs.KeccakInjective
import specs.KeccakDistinct
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_update_fold_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_pad_user

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

/-- `sstore` does not touch the collision flag. -/
private lemma hash_collision_sstore (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).hash_collision = σ.hash_collision := by
  unfold EVMState.sstore
  cases h : σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-- The innermost hash flag of a padding step (the push's internal slot hash). -/
def padFinClean (σ : EVMState) (i : UInt256) : Prop :=
  (arrOut ((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
      ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))
    ((arrOut σ 2).1 + i)).2.hash_collision = false

/-- **The padding step preserves low slots** (A6″ + frames): both of its
stores land at keccak-plus-small-offset slots. -/
lemma padStep_sload_low
    {σ : EVMState} {i s : UInt256}
    (hs : s.val < lowSlotBound)
    (hi : i.val < lowSlotBound)
    (hlen : (((arrOut (arrOut σ 2).2 3).2).sload ((arrOut σ 2).1 + i)).val < lowSlotBound)
    (hfin : padFinClean σ i) :
    ((padStep σ i).sload s) = σ.sload s := by
  unfold padFinClean at hfin
  -- backward cleanliness chain
  have hE1 : (((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
      ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))).hash_collision = false :=
    arrOut_clean_backward hfin
  have hB : ((arrOut (arrOut σ 2).2 3).2).hash_collision = false := by
    rwa [hash_collision_sstore] at hE1
  have hA : ((arrOut σ 2).2).hash_collision = false := arrOut_clean_backward hB
  -- keccak witnesses for the two written slots
  have hksomeFin := keccakOut_some_of_clean
    (σ := (((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
        ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))).mstore 0
      ((arrOut σ 2).1 + i)) (p := 0) (n := 32) (by exact hfin)
  have hpairFin : ((((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
        ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))).mstore 0
      ((arrOut σ 2).1 + i)).keccak256 0 32
      = some ((arrOut ((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
          ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))
          ((arrOut σ 2).1 + i)).1,
        (arrOut ((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
          ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))
          ((arrOut σ 2).1 + i)).2) := by
    rw [hksomeFin]
    rfl
  have hksomeA := keccakOut_some_of_clean
    (σ := σ.mstore 0 2) (p := 0) (n := 32) (by exact hA)
  have hpairA : (σ.mstore 0 2).keccak256 0 32
      = some ((arrOut σ 2).1, (arrOut σ 2).2) := by
    rw [hksomeA]
    rfl
  -- the two stored slots miss `s`
  have hne1 : (arrOut ((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
      ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))
      ((arrOut σ 2).1 + i)).1
      + ((arrOut (arrOut σ 2).2 3).2).sload ((arrOut σ 2).1 + i) ≠ s :=
    keccak256_add_ne_lowSlot _ s hpairFin hlen hs
  have hne2 : (arrOut σ 2).1 + i ≠ s :=
    keccak256_add_ne_lowSlot i s hpairA hi hs
  show ((pushEvm (arrOut (arrOut σ 2).2 3).2 ((arrOut σ 2).1 + i)
      ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut (arrOut σ 2).2 3).1 + i))).sload s)
    = σ.sload s
  unfold pushEvm
  rw [Clear.KeccakDistinct.sload_sstore_of_ne _ (Ne.symm hne1)]
  rw [sload_arrOut_of_clean s hfin]
  rw [Clear.KeccakDistinct.sload_sstore_of_ne _ (Ne.symm hne2)]
  rw [sload_arrOut_of_clean s hB]
  rw [sload_arrOut_of_clean s hA]

/-- Per-pass discharge conditions of the padding walk. -/
def PadLowOK (t : EVMState × UInt256 × UInt256 × UInt256) : Prop :=
  t.2.1.val < lowSlotBound ∧
  (((arrOut (arrOut t.1 2).2 3).2).sload ((arrOut t.1 2).1 + t.2.1)).val < lowSlotBound ∧
  padFinClean t.1 t.2.1

/-- **THE PADDING WALK PRESERVES EVERY LOW SLOT** (A6″). -/
lemma padWalk_sload_low :
    ∀ (kk : ℕ) {σ : EVMState} {i om m s : UInt256},
    s.val < lowSlotBound →
    (∀ j, j < kk → PadLowOK (padWalk j σ i om m)) →
    ((padWalk kk σ i om m).1).sload s = σ.sload s := by
  intro kk
  induction kk with
  | zero =>
    intro σ i om m s _ _
    rfl
  | succ kk ih =>
    intro σ i om m s hs hok
    have h0 := hok 0 (by omega)
    simp only [padWalk] at h0 ⊢
    rw [ih hs (by
      intro j hj
      have := hok (j+1) (by omega)
      simpa only [padWalk] using this)]
    exact padStep_sload_low hs h0.1 h0.2.1 h0.2.2

/-! ## The low-slot frames on the derived route

Everything in this file reaches `keccak256_add_ne_lowSlot`: the write of a walk level
lands at `keccak(levelArray) + j`, and A6″ is what says such a slot is never a reserved
low one.  `keccak256_add_ne_lowSlot_of_config` says the same from two pool facts —
`RangeInWindow` (the unused pool sits clear of both ends of the address space) and
`CachedInWindow` (so does everything already cached).

These twins thread that pair down the same call tree.  The transport across the two
walks and the hash atoms is what made them statable. -/

/-- **DERIVED** companion to `nodeStore_sload_low`. -/
lemma nodeStore_sload_low_of_config
    {σ : EVMState} {base l j v s : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ)
    (hC : Clear.KeccakLowSlot.CachedInWindow σ)
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
    Clear.KeccakLowSlot.keccak256_add_ne_lowSlot_of_config j s
      (Clear.KeccakLowSlot.rangeInWindow_mstore 0 _ (rangeInWindow_arrOut hR))
      (Clear.KeccakLowSlot.cachedInWindow_mstore 0 _
        (cachedInWindow_arrOut hR hC))
      hpair hj hs
  rw [Clear.KeccakDistinct.sload_sstore_of_ne _ (Ne.symm hne)]
  rw [sload_arrOut_of_clean s hclean]
  rw [sload_arrOut_of_clean s hcleanA]

/-- **DERIVED** companion to `stepOdd_sload_low`. -/
lemma stepOdd_sload_low_of_config
    {σ : EVMState} {base i idx cur s : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ)
    (hC : Clear.KeccakLowSlot.CachedInWindow σ)
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
  have hR' : Clear.KeccakLowSlot.RangeInWindow (accOut (sibRead σ base i (idx - 1)).2 (sibRead σ base i (idx - 1)).1 cur).2 :=
    (rangeInWindow_accOut (rangeInWindow_arrOut (rangeInWindow_arrOut hR)))
  have hC' : Clear.KeccakLowSlot.CachedInWindow (accOut (sibRead σ base i (idx - 1)).2 (sibRead σ base i (idx - 1)).1 cur).2 :=
    (cachedInWindow_accOut (rangeInWindow_arrOut (rangeInWindow_arrOut hR))
      (cachedInWindow_arrOut (rangeInWindow_arrOut hR) (cachedInWindow_arrOut hR hC)))
  rw [nodeStore_sload_low_of_config hR' hC' hfin h4 hj hs]
  rw [sload_accOut_of_clean s h3]
  show ((arrOut (arrOut σ base).2 ((arrOut σ base).1 + i)).2).sload s = σ.sload s
  rw [sload_arrOut_of_clean s h2]
  rw [sload_arrOut_of_clean s h1]

/-- **DERIVED** companion to `stepEven_sload_low`. -/
lemma stepEven_sload_low_of_config
    {σ : EVMState} {base i idx cur s : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ)
    (hC : Clear.KeccakLowSlot.CachedInWindow σ)
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
  have hR' : Clear.KeccakLowSlot.RangeInWindow (accOut (sibRead σ base i (idx + 1)).2 cur (sibRead σ base i (idx + 1)).1).2 :=
    (rangeInWindow_accOut (rangeInWindow_arrOut (rangeInWindow_arrOut hR)))
  have hC' : Clear.KeccakLowSlot.CachedInWindow (accOut (sibRead σ base i (idx + 1)).2 cur (sibRead σ base i (idx + 1)).1).2 :=
    (cachedInWindow_accOut (rangeInWindow_arrOut (rangeInWindow_arrOut hR))
      (cachedInWindow_arrOut (rangeInWindow_arrOut hR) (cachedInWindow_arrOut hR hC)))
  rw [nodeStore_sload_low_of_config hR' hC' hfin h4 hj hs]
  rw [sload_accOut_of_clean s h3]
  show ((arrOut (arrOut σ base).2 ((arrOut σ base).1 + i)).2).sload s = σ.sload s
  rw [sload_arrOut_of_clean s h2]
  rw [sload_arrOut_of_clean s h1]

/-- **DERIVED** companion to `stepEdge_sload_low`. -/
lemma stepEdge_sload_low_of_config
    {σ : EVMState} {ss base i idx cur s : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ)
    (hC : Clear.KeccakLowSlot.CachedInWindow σ)
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
  have hR' : Clear.KeccakLowSlot.RangeInWindow (accOut (sideRead σ (ss + 3) i).2 cur (sideRead σ (ss + 3) i).1).2 :=
    (rangeInWindow_accOut (rangeInWindow_arrOut hR))
  have hC' : Clear.KeccakLowSlot.CachedInWindow (accOut (sideRead σ (ss + 3) i).2 cur (sideRead σ (ss + 3) i).1).2 :=
    (cachedInWindow_accOut (rangeInWindow_arrOut hR) (cachedInWindow_arrOut hR hC))
  rw [nodeStore_sload_low_of_config hR' hC' hfin h4 hj hs]
  rw [sload_accOut_of_clean s h3]
  show ((arrOut σ (ss + 3)).2).sload s = σ.sload s
  rw [sload_arrOut_of_clean s h2]

/-- **DERIVED** companion to `updateStep_sload_low`. -/
lemma updateStep_sload_low_of_config
    {σ : EVMState} {ss base i idx maxN cur s : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ)
    (hC : Clear.KeccakLowSlot.CachedInWindow σ)
    (hs : s.val < lowSlotBound)
    (hok : StepLowOK ss base (σ, i, idx, maxN, cur)) :
    ((updateStep σ ss base i idx maxN cur).2).sload s = σ.sload s := by
  obtain ⟨hj, hflag⟩ := hok
  unfold updateStep
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge]
      rw [if_pos hpar, if_pos hedge] at hflag
      exact stepEdge_sload_low_of_config hR hC hs hj hflag
    · rw [if_pos hpar, if_neg hedge]
      rw [if_pos hpar, if_neg hedge] at hflag
      exact stepEven_sload_low_of_config hR hC hs hj hflag
  · rw [if_neg hpar]
    rw [if_neg hpar] at hflag
    exact stepOdd_sload_low_of_config hR hC hs hj hflag

/-- **THE WALK PRESERVES EVERY LOW SLOT — DERIVED.**  The induction re-establishes the
window pair at each level from `rangeInWindow_updateStep` / `cachedInWindow_updateStep`. -/
lemma updateWalk_sload_low_of_config :
    ∀ (kk : ℕ) {σ : EVMState} {ss base i idx maxN cur s : UInt256},
    Clear.KeccakLowSlot.RangeInWindow σ →
    Clear.KeccakLowSlot.CachedInWindow σ →
    s.val < lowSlotBound →
    (∀ j, j < kk → StepLowOK ss base (updateWalk ss base j σ i idx maxN cur)) →
    ((updateWalk ss base kk σ i idx maxN cur).1).sload s = σ.sload s := by
  intro kk
  induction kk with
  | zero =>
    intro σ ss base i idx maxN cur s _ _ _ _
    rfl
  | succ kk ih =>
    intro σ ss base i idx maxN cur s hR hC hs hok
    have h0 := hok 0 (by omega)
    simp only [updateWalk] at h0 ⊢
    rw [ih (rangeInWindow_updateStep hR) (cachedInWindow_updateStep hR hC) hs (by
      intro j hj
      have := hok (j+1) (by omega)
      simpa only [updateWalk] using this)]
    exact updateStep_sload_low_of_config hR hC hs h0

/-- **DERIVED** companion to `padStep_sload_low`. -/
lemma padStep_sload_low_of_config
    {σ : EVMState} {i s : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ)
    (hC : Clear.KeccakLowSlot.CachedInWindow σ)
    (hs : s.val < lowSlotBound)
    (hi : i.val < lowSlotBound)
    (hlen : (((arrOut (arrOut σ 2).2 3).2).sload ((arrOut σ 2).1 + i)).val < lowSlotBound)
    (hfin : padFinClean σ i) :
    ((padStep σ i).sload s) = σ.sload s := by
  unfold padFinClean at hfin
  have hE1 : (((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
      ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))).hash_collision = false :=
    arrOut_clean_backward hfin
  have hB : ((arrOut (arrOut σ 2).2 3).2).hash_collision = false := by
    rwa [hash_collision_sstore] at hE1
  have hA : ((arrOut σ 2).2).hash_collision = false := arrOut_clean_backward hB
  have hksomeFin := keccakOut_some_of_clean
    (σ := (((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
        ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))).mstore 0
      ((arrOut σ 2).1 + i)) (p := 0) (n := 32) (by exact hfin)
  have hpairFin : ((((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
        ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))).mstore 0
      ((arrOut σ 2).1 + i)).keccak256 0 32
      = some ((arrOut ((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
          ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))
          ((arrOut σ 2).1 + i)).1,
        (arrOut ((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
          ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))
          ((arrOut σ 2).1 + i)).2) := by
    rw [hksomeFin]
    rfl
  have hksomeA := keccakOut_some_of_clean
    (σ := σ.mstore 0 2) (p := 0) (n := 32) (by exact hA)
  have hpairA : (σ.mstore 0 2).keccak256 0 32
      = some ((arrOut σ 2).1, (arrOut σ 2).2) := by
    rw [hksomeA]
    rfl
  have hne1 : (arrOut ((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
      ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))
      ((arrOut σ 2).1 + i)).1
      + ((arrOut (arrOut σ 2).2 3).2).sload ((arrOut σ 2).1 + i) ≠ s :=
    Clear.KeccakLowSlot.keccak256_add_ne_lowSlot_of_config _ s
      (Clear.KeccakLowSlot.rangeInWindow_mstore 0 _
        (Clear.StorageFrame.rangeInWindow_sstore
          (rangeInWindow_arrOut (rangeInWindow_arrOut hR))))
      (Clear.KeccakLowSlot.cachedInWindow_mstore 0 _
        (Clear.StorageFrame.cachedInWindow_sstore
          (cachedInWindow_arrOut (rangeInWindow_arrOut hR)
            (cachedInWindow_arrOut hR hC))))
      hpairFin hlen hs
  have hne2 : (arrOut σ 2).1 + i ≠ s :=
    Clear.KeccakLowSlot.keccak256_add_ne_lowSlot_of_config i s
      (Clear.KeccakLowSlot.rangeInWindow_mstore 0 2 hR)
      (Clear.KeccakLowSlot.cachedInWindow_mstore 0 2 hC)
      hpairA hi hs
  show ((pushEvm (arrOut (arrOut σ 2).2 3).2 ((arrOut σ 2).1 + i)
      ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut (arrOut σ 2).2 3).1 + i))).sload s)
    = σ.sload s
  unfold pushEvm
  rw [Clear.KeccakDistinct.sload_sstore_of_ne _ (Ne.symm hne1)]
  rw [sload_arrOut_of_clean s hfin]
  rw [Clear.KeccakDistinct.sload_sstore_of_ne _ (Ne.symm hne2)]
  rw [sload_arrOut_of_clean s hB]
  rw [sload_arrOut_of_clean s hA]

/-- **THE PADDING WALK PRESERVES EVERY LOW SLOT — DERIVED.** -/
lemma padWalk_sload_low_of_config :
    ∀ (kk : ℕ) {σ : EVMState} {i om m s : UInt256},
    Clear.KeccakLowSlot.RangeInWindow σ →
    Clear.KeccakLowSlot.CachedInWindow σ →
    s.val < lowSlotBound →
    (∀ j, j < kk → PadLowOK (padWalk j σ i om m)) →
    ((padWalk kk σ i om m).1).sload s = σ.sload s := by
  intro kk
  induction kk with
  | zero =>
    intro σ i om m s _ _ _ _
    rfl
  | succ kk ih =>
    intro σ i om m s hR hC hs hok
    have h0 := hok 0 (by omega)
    simp only [padWalk] at h0 ⊢
    rw [ih (rangeInWindow_padStep hR) (cachedInWindow_padStep hR hC) hs (by
      intro j hj
      have := hok (j+1) (by omega)
      simpa only [padWalk] using this)]
    exact padStep_sload_low_of_config hR hC hs h0.1 h0.2.1 h0.2.2

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
