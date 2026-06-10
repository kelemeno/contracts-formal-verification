import Clear.EVMState
import Clear.State

/-
  RevertModel.lean — foundational lemmas about the new `reverted` flag on
  `EVMState`.

  The Clear EVM model historically left a reverting execution in an `Ok` state
  (revert only rewrites `return_data`), so success could not be distinguished
  from failure by `isOk`.  The framework now carries a boolean `reverted` field
  on `EVMState`:

    * `evm_revert σ a b := { σ.evm_return a b with reverted := true }`
      — ANY revert sets `reverted := true`.
    * every other EVM op updates with `{ σ with … }` syntax, which PRESERVES
      `reverted`.

  This file proves the minimal facts needed to phrase guard theorems in the
  clean "success ⇒ precondition held" form, plus two convenience predicates.
-/

namespace Clear.RevertModel

open Clear EVMState State

variable (σ : EVMState)

/-- A revert always yields `reverted = true`. -/
@[simp] lemma evm_revert_reverted (a b : UInt256) :
    (σ.evm_revert a b).reverted = true := rfl

/-- `evm_return` (the non-reverting variant) preserves the flag. -/
@[simp] lemma evm_return_reverted (a b : UInt256) :
    (σ.evm_return a b).reverted = σ.reverted := rfl

/-- `mstore` preserves the flag (it is a `{ σ with … }` update). -/
@[simp] lemma mstore_reverted (a v : UInt256) :
    (σ.mstore a v).reverted = σ.reverted := rfl

/-- `sstore` preserves the flag on both match branches. -/
@[simp] lemma sstore_reverted (a v : UInt256) :
    (σ.sstore a v).reverted = σ.reverted := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner <;> rfl

/-- `setEvm` writes the supplied evm verbatim, so the resulting state's evm is
    exactly that evm (on an `Ok` state). -/
@[simp] lemma evm_setEvm_ok {evm evm₀ : EVM} {store : VarStore} :
    (State.setEvm evm (Ok evm₀ store)).evm = evm := rfl

/-- A (Ok-shaped) state's evm flag after a revert primop is `true`. -/
lemma reverted_of_revert_setEvm {evm₀ : EVM} {store : VarStore} (a b : UInt256) :
    (State.setEvm (evm₀.evm_revert a b) (Ok evm₀ store)).evm.reverted = true := rfl

-- ============================================================================
--  Convenience predicates
-- ============================================================================

/-- The state did not revert (and any non-`Ok` state vacuously has `evm = default`
    whose `reverted = false`). -/
def State.notReverted (s : State) : Prop := ¬ s.evm.reverted

/-- A genuinely successful execution: `Ok` AND not reverted. -/
def State.succeeded (s : State) : Prop := s.isOk ∧ ¬ s.evm.reverted

end Clear.RevertModel
