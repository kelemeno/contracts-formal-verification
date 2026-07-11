import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_update_fold_user

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

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
