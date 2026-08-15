import specs.KeccakDeterminism

/-! # The clean flag as a composable currency

Clear does not model an exhausted keccak pool as a failure: `keccak256` returns `none`,
and `primCall .Keccak256` then hands back `0` on a state carrying `hash_collision := True`.
The state is still `Ok`.  So "no hash on this path exhausted the pool" is not something
`isOk` can tell you -- but it IS observable, as a single boolean on the final state.

That makes it a better currency than a fuel budget for the deep call chains here.  A budget
has to be decided in advance and decremented through every callee; worse, when the chain
contains a loop the budget is `6 * k` for a trip count `k` that only the loop's own
induction reveals, so a caller outside the loop cannot discharge it at all.  The flag is a
property of the state in hand, and it travels BACKWARDS: if the end of the chain is clean,
every step of it was.

This file collects the backward-propagation lemmas.  Everything except a hash preserves the
flag definitionally; a hash preserves it exactly when it succeeded, which is the content of
`KeccakDeterminism.keccakOut_clean_backward`. -/

namespace Clear.KeccakClean

open Clear EVMState

/-- No hash along the way exhausted the pool. -/
abbrev Clean (σ : EVMState) : Prop := σ.hash_collision = false

@[simp] theorem clean_mstore (σ : EVMState) (a v : UInt256) :
    Clean (σ.mstore a v) ↔ Clean σ := Iff.rfl

@[simp] theorem clean_sstore (σ : EVMState) (p v : UInt256) :
    Clean (σ.sstore p v) ↔ Clean σ := by
  -- `sstore` branches on whether the account exists, and neither branch touches the flag
  unfold EVMState.sstore
  rcases EVMState.lookupAccount σ σ.execution_env.code_owner with _ | act
  · exact Iff.rfl
  · exact Iff.rfl

@[simp] theorem clean_mstore8 (σ : EVMState) (a v : UInt256) :
    Clean (σ.mstore8 a v) ↔ Clean σ := Iff.rfl

@[simp] theorem clean_evm_return (σ : EVMState) (p n : UInt256) :
    Clean (σ.evm_return p n) ↔ Clean σ := Iff.rfl

/-- A revert is a flag in this model, not a rollback -- so it carries the collision flag
across unchanged, exactly as it carries the storage. -/
@[simp] theorem clean_evm_revert (σ : EVMState) (p n : UInt256) :
    Clean (σ.evm_revert p n) ↔ Clean σ := Iff.rfl

/-- **The one step that can break it**, and the direction that matters: a clean post-state
forces a clean pre-state, because the only way the flag can turn on is a hash that found the
pool empty. -/
theorem clean_keccakOut_backward {σ : EVMState} {p n : UInt256}
    (h : Clean (KeccakDeterminism.keccakOut σ p n).2) : Clean σ :=
  KeccakDeterminism.keccakOut_clean_backward h

/-- ...and the same hypothesis says the hash genuinely succeeded, which is what every
freshness argument downstream actually needs. -/
theorem keccak256_some_of_clean {σ : EVMState} {p n : UInt256}
    (h : Clean (KeccakDeterminism.keccakOut σ p n).2) :
    σ.keccak256 p n = some (KeccakDeterminism.keccakOut σ p n) :=
  KeccakDeterminism.keccakOut_some_of_clean h

/-- A hash run on a memory write, which is the shape every array accessor has.  Stated with
the `mstore` peeled by `clean_mstore` rather than by unification -- letting the elaborator
see through both at once sends `whnf` into the memory model. -/
theorem clean_of_keccakOut_mstore {σ : EVMState} {a v p n : UInt256}
    (h : Clean (KeccakDeterminism.keccakOut (σ.mstore a v) p n).2) : Clean σ := by
  have := clean_keccakOut_backward h
  rwa [clean_mstore] at this

end Clear.KeccakClean
