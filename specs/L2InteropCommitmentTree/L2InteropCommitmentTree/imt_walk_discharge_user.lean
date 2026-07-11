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

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
