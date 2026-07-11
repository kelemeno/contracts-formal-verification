import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_update_fold_user
import specs.AtomicFlowManager.AtomicFlowManager.imt_path_user

/-
  BUILDER–VERIFIER AGREEMENT, layer 1 — the one-level replay atoms.

  The walk caches each level's pair hash (`accOut_caches_of_clean`); a later
  verifier fold re-computes the same pair on its own evm.  Provided (i) the
  verifier's keccak cache contains the walk's entries (cache transport) and
  (ii) the two evms agree on the scratch junk window `[64, 95)` (the only
  bytes of the hash preimage not overwritten by the pair `mstore`s), the fold
  step is a CACHE HIT returning the walk's value, and it leaves the cache
  untouched — so hits chain.  These are the induction atoms for the agreement
  theorem `foldRoot`-over-walk-siblings = walk root.

  Axiom-free.
-/

namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-- **One-level cross-evm agreement.**  If the pair `(a, b)`'s hash is cached
(under the *walk-side* memory `σw`) with value `r`, the cache has been
transported into the verifier evm `σv`, and the two evms agree on the junk
window, then the verifier's pair-hash step returns exactly `r`. -/
theorem accOut_agree
    {σv σw : EVMState} {a b r : UInt256}
    (hjunk : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σv.machine_state.memory
        = Finmap.lookup i σw.machine_state.memory)
    (hcached : Finmap.lookup (accInterval σw a b) σv.keccak_map = some r) :
    accOut σv a b = (r, (σv.mstore 0 a).mstore 32 b) := by
  apply accOut_of_cached
  rw [accInterval_eq hjunk]
  exact hcached

/-- A cache-hit pair-hash step leaves the keccak cache untouched — hits chain. -/
theorem accOut_cached_keccak_map
    {σ : EVMState} {a b r : UInt256}
    (hcached : Finmap.lookup (accInterval σ a b) σ.keccak_map = some r) :
    (accOut σ a b).2.keccak_map = σ.keccak_map := by
  rw [accOut_of_cached hcached]
  rfl

/-- A cache-hit pair-hash step preserves the junk window `[64, 95)`. -/
theorem accOut_cached_junk
    {σ : EVMState} {a b r : UInt256} {i : UInt256}
    (hcached : Finmap.lookup (accInterval σ a b) σ.keccak_map = some r)
    (hi : 64 ≤ i.val) :
    Finmap.lookup i (accOut σ a b).2.machine_state.memory
      = Finmap.lookup i σ.machine_state.memory :=
  accOut_junk_window hi

/-- A pair-hash step preserves all path-array reads (`≥ 96`). -/
theorem accOut_path_read
    {σ : EVMState} {a b p' : UInt256}
    (hp : 96 ≤ p'.val) (hnw : p'.val + 32 ≤ 2 ^ 256) :
    (accOut σ a b).2.mload p' = σ.mload p' :=
  accOut_mload_high hp hnw

/-- The verifier fold as a tuple walk `(evm, i, idx, cur)` — the prefix-state
form needed for induction-friendly hypotheses. -/
def foldWalk (p : UInt256) : ℕ → EVMState → UInt256 → UInt256 → UInt256
    → EVMState × UInt256 × UInt256 × UInt256
  | 0, σ, i, idx, cur => (σ, i, idx, cur)
  | (j+1), σ, i, idx, cur =>
      foldWalk p j
        (if Fin.land idx 1 = 0
          then accOut σ cur (σ.mload ((p + Fin.shiftLeft i 5) + 32))
          else accOut σ (σ.mload ((p + Fin.shiftLeft i 5) + 32)) cur).2
        (i + 1) (Fin.shiftRight idx 1)
        (if Fin.land idx 1 = 0
          then accOut σ cur (σ.mload ((p + Fin.shiftLeft i 5) + 32))
          else accOut σ (σ.mload ((p + Fin.shiftLeft i 5) + 32)) cur).1

/-- `foldWalk` computes `foldRoot`. -/
lemma foldWalk_foldRoot :
    ∀ (k : ℕ) {σ : EVMState} {p i idx cur : UInt256},
    (foldWalk p k σ i idx cur).2.2.2 = (generated.AtomicFlowManager.AtomicFlowManager.foldRoot σ p k i idx cur).1
      ∧ (foldWalk p k σ i idx cur).1 = (generated.AtomicFlowManager.AtomicFlowManager.foldRoot σ p k i idx cur).2 := by
  intro k
  induction k with
  | zero =>
    intro σ p i idx cur
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro σ p i idx cur
    simp only [foldWalk, generated.AtomicFlowManager.AtomicFlowManager.foldRoot]
    by_cases hpar : Fin.land idx 1 = 0
    · simp only [if_pos hpar]
      exact ih
    · simp only [if_neg hpar]
      exact ih

/-- The sibling value one walk level reads (dispatched). -/
def walkSib (ss base : UInt256)
    (t : EVMState × UInt256 × UInt256 × UInt256 × UInt256) : UInt256 :=
  if Fin.land t.2.2.1 1 = 0 then
    (if t.2.2.2.1 = t.2.2.1 then (sideRead t.1 (ss + 3) t.2.1).1
     else (sibRead t.1 base t.2.1 (t.2.2.1 + 1)).1)
  else (sibRead t.1 base t.2.1 (t.2.2.1 - 1)).1

/-- The pair-hash output one walk level produces (dispatched — equals the
next walk `cur`). -/
def walkHash (ss base : UInt256)
    (t : EVMState × UInt256 × UInt256 × UInt256 × UInt256) : UInt256 × EVMState :=
  if Fin.land t.2.2.1 1 = 0 then
    (if t.2.2.2.1 = t.2.2.1 then
      accOut (sideRead t.1 (ss + 3) t.2.1).2 t.2.2.2.2 (sideRead t.1 (ss + 3) t.2.1).1
     else accOut (sibRead t.1 base t.2.1 (t.2.2.1 + 1)).2 t.2.2.2.2
        (sibRead t.1 base t.2.1 (t.2.2.1 + 1)).1)
  else accOut (sibRead t.1 base t.2.1 (t.2.2.1 - 1)).2
      (sibRead t.1 base t.2.1 (t.2.2.1 - 1)).1 t.2.2.2.2

private lemma arrOut_lookup_mono
    {σ : EVMState} {a : UInt256} {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (arrOut σ a).2.keccak_map = some w := by
  apply keccakOut_lookup_mono
  rwa [keccak_map_mstore]

/-- `sstore` does not touch the keccak cache. -/
private lemma keccak_map_sstore (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).keccak_map = σ.keccak_map := by
  unfold EVMState.sstore
  cases h : σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-- One walk step only grows the keccak cache. -/
lemma updateStep_lookup_mono
    {σ : EVMState} {ss base i idx maxN cur : UInt256} {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I ((updateStep σ ss base i idx maxN cur).2).keccak_map = some w := by
  unfold updateStep
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge]
      unfold stepEdge nodeStore sideRead
      rw [keccak_map_sstore]
      exact arrOut_lookup_mono (arrOut_lookup_mono (accOut_lookup_mono
        (arrOut_lookup_mono hI)))
    · rw [if_pos hpar, if_neg hedge]
      unfold stepEven nodeStore sibRead
      rw [keccak_map_sstore]
      exact arrOut_lookup_mono (arrOut_lookup_mono (accOut_lookup_mono
        (arrOut_lookup_mono (arrOut_lookup_mono hI))))
  · rw [if_neg hpar]
    unfold stepOdd nodeStore sibRead
    rw [keccak_map_sstore]
    exact arrOut_lookup_mono (arrOut_lookup_mono (accOut_lookup_mono
      (arrOut_lookup_mono (arrOut_lookup_mono hI))))

/-- The whole walk only grows the keccak cache. -/
lemma updateWalk_lookup_mono :
    ∀ (k : ℕ) {σ : EVMState} {ss base i idx maxN cur : UInt256}
      {I : List UInt256} {w : UInt256},
    Finmap.lookup I σ.keccak_map = some w →
    Finmap.lookup I ((updateWalk ss base k σ i idx maxN cur).1).keccak_map = some w := by
  intro k
  induction k with
  | zero =>
    intro σ ss base i idx maxN cur I w hI
    exact hI
  | succ k ih =>
    intro σ ss base i idx maxN cur I w hI
    simp only [updateWalk]
    exact ih (updateStep_lookup_mono hI)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
