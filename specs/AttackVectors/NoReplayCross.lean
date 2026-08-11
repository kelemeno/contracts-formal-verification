import specs.AttackVectors.NestedSlots
import specs.L1Nullifier.L1Nullifier.no_replay_user

/-
  A FINALIZED WITHDRAWAL STAYS FINALIZED — across other withdrawals' writes.

  `L1Nullifier.replay_after_set_reverts` proves a withdrawal cannot be re-finalized AT ITS OWN SLOT,
  and `check_set_slots_eq` proves the slot set is the slot later checked.  Both are same-slot
  statements, honestly so.

  The remaining question is cross-withdrawal, and it is the drain-relevant direction: could finalizing
  some OTHER withdrawal clear this one's flag and re-open the replay?  `NestedSlots`'s three-level
  separation says no — the flags live at different slots — and this file composes that with the replay
  check so the conclusion is a revert rather than a state fact.

  Axiom-free.
-/

namespace AttackVectors.NoReplayCross

open Clear Clear.KeccakDeterminism Clear.KeccakFresh
open AttackVectors.NestedSlots
open EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas

/-- **A SET FLAG SURVIVES ANOTHER WITHDRAWAL'S FINALIZATION.**  If this withdrawal's finalized byte is
nonzero, it is still nonzero after a write at a different withdrawal's slot. -/
theorem finalized_stays_finalized {σ σ_w : EVMState} (hinj : CacheInj σ)
    {c₁ c₂ n₁ n₂ x₁ x₂ base p₁ p₂ q₁ q₂ r₁ r₂ v : UInt256}
    (hp₁ : Finmap.lookup (accInterval σ c₁ base) σ.keccak_map = some p₁)
    (hp₂ : Finmap.lookup (accInterval σ c₂ base) σ.keccak_map = some p₂)
    (hq₁ : Finmap.lookup (accInterval σ n₁ p₁) σ.keccak_map = some q₁)
    (hq₂ : Finmap.lookup (accInterval σ n₂ p₂) σ.keccak_map = some q₂)
    (hr₁ : Finmap.lookup (accInterval σ x₁ q₁) σ.keccak_map = some r₁)
    (hr₂ : Finmap.lookup (accInterval σ x₂ q₂) σ.keccak_map = some r₂)
    (hne : c₁ ≠ c₂ ∨ n₁ ≠ n₂ ∨ x₁ ≠ x₂)
    (hset : Fin.land (σ_w.sload r₂) 255 ≠ 0) :
    Fin.land ((σ_w.sstore r₁ v).sload r₂) 255 ≠ 0 := by
  rw [finalize_frames_other_withdrawal hinj hp₁ hp₂ hq₁ hq₂ hr₁ hr₂ hne]
  exact hset

/-- **NO REPLAY RE-OPENED BY ANOTHER WITHDRAWAL.**  After some other withdrawal is finalized, the
replay CHECK for this one still reverts.

This is the composition `replay_after_set_reverts` does not make: that theorem shows a withdrawal
cannot be replayed at its own slot, with nothing else touching storage.  This shows the protection
survives an attacker finalizing whatever else they can — the flags do not alias, so the guard still
fires. -/
theorem replay_still_reverts_after_other_finalization
    {σ σ_w : EVMState} (hinj : CacheInj σ)
    {c₁ c₂ n₁ n₂ x₁ x₂ base p₁ p₂ q₁ q₂ r₁ r₂ v : UInt256}
    {store : VarStore} {fuel : ℕ} {s₉ : State} {key : Literal}
    (hp₁ : Finmap.lookup (accInterval σ c₁ base) σ.keccak_map = some p₁)
    (hp₂ : Finmap.lookup (accInterval σ c₂ base) σ.keccak_map = some p₂)
    (hq₁ : Finmap.lookup (accInterval σ n₁ p₁) σ.keccak_map = some q₁)
    (hq₂ : Finmap.lookup (accInterval σ n₂ p₂) σ.keccak_map = some q₂)
    (hr₁ : Finmap.lookup (accInterval σ x₁ q₁) σ.keccak_map = some r₁)
    (hr₂ : Finmap.lookup (accInterval σ x₂ q₂) σ.keccak_map = some r₂)
    (hne : c₁ ≠ c₂ ∨ n₁ ≠ n₂ ∨ x₁ ≠ x₂)
    (hset : Fin.land (σ_w.sload r₂) 255 ≠ 0)
    (hslot : (Ok (σ_w.sstore r₁ v) store)["split_expr_7"]!! = r₂)
    (hkey : (Ok (σ_w.sstore r₁ v) store)["_1"]!! = key)
    (hexec : exec (fuel+1)
      L1Nullifier.Common.block_4604436955705083701
      (Ok (σ_w.sstore r₁ v) store) = s₉) :
    s₉.evm.reverted = true :=
  generated.L1Nullifier.L1Nullifier.replay_protection_check_reverts hslot hkey
    (finalized_stays_finalized hinj hp₁ hp₂ hq₁ hq₂ hr₁ hr₂ hne hset) hexec

end AttackVectors.NoReplayCross
