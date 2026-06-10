import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_6547236921511043342

import generated.L1Bridgehub.L1Bridgehub.fun_requireNotPaused_gen


/-
  Formal spec for the Yul translation of L1Bridgehub._requireNotPaused
  (OpenZeppelin Pausable._requireNotPaused()):
      require(!paused(), "Pausable: paused");

  Yul (see fun_requireNotPaused_gen.lean):
      let split_expr_0 := sload(151)            -- Pausable._paused storage slot 151
      let split_expr_1 := and(split_expr_0, 255) -- low byte: the bool `paused`
      let split_expr_2 := iszero(split_expr_1)   -- paused == 0 ?
      if iszero(split_expr_2) { ...revert... }   -- if paused != 0, revert

  Storage slot: 151.  Bool mask: 255 (Fin.land (sload 151) 255).
  The contract is NOT paused iff  Fin.land (evm.sload 151) 255 = 0.

  Abstract spec: a successful (non-reverting) execution implies the contract is
  not paused.  Because a revert in this model still yields an `Ok` state (it only
  rewrites return_data), we characterise success as "the state was not modified":
  the function leaves storage/evm untouched on the non-revert path, while the
  revert path runs the if-block and changes the state.  Hence

      either NOT paused (paused byte = 0),  OR  s₉ ≠ s₀ (the revert branch ran).
-/

namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common

-- Post-sload state entering the `if iszero(split_expr_2)` revert guard:
-- split_expr_0 := sload(151); split_expr_1 := and(split_expr_0, 255);
-- split_expr_2 := iszero(split_expr_1).
def fun_requireNotPaused_preState (evm : EVM) : State :=
  let b := Fin.land (sload evm 151) 255
  (Ok evm (Inhabited.default : VarStore))
    ⟦"split_expr_0" ↦ sload evm 151⟧
    ⟦"split_expr_1" ↦ b⟧
    ⟦"split_expr_2" ↦ (decide (b = 0)).toUInt256⟧

-- Abstract spec for OpenZeppelin `_requireNotPaused()`:
--   require(!paused(), "Pausable: paused").
-- Storage slot 151 holds the Pausable bool in its low byte (mask 255).
-- The contract is NOT paused iff  Fin.land (sload evm 151) 255 = 0.
--
-- Meaning: from any starting state `Ok evm store`, EITHER the contract is not
-- paused, OR execution took the revert branch — witnessed by the inner `if`
-- block (if_6547236921511043342, the `revert(...)` body) running from the
-- post-sload state and producing the final state s₉.  In particular a run that
-- does NOT go through the revert if-block forces the not-paused disjunct.
def A_fun_requireNotPaused   (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    ( Fin.land (sload evm 151) 255 = 0
      ∨ ∃ ss, Spec A_if_6547236921511043342 (fun_requireNotPaused_preState evm) ss ∧
              s₉ = (match reviveJump ss, Ok evm store with
                     | Ok e _, Ok _ st => Ok e st
                     | s, _ => s) )

lemma fun_requireNotPaused_abs_of_concrete {s₀ s₉ : State}  :
  Spec (fun_requireNotPaused_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_fun_requireNotPaused  ) s₀ s₉ := by
  unfold fun_requireNotPaused_concrete_of_code A_fun_requireNotPaused
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete evmA storeA hok
  -- hok : Ok evm store = Ok evmA storeA
  cases hok
  -- We always provide the if-block witness (right disjunct).
  refine Or.inr ?_
  clr_funargs at hconcrete
  obtain ⟨ss, hspec, hmerge⟩ := hconcrete
  refine ⟨ss, ?_, ?_⟩
  · -- The witness pre-state in `hconcrete` equals `fun_requireNotPaused_preState evm`.
    convert hspec using 2
  · -- The merge expression matches (same match, alpha-renamed).
    rw [← hmerge]
    rcases (reviveJump ss) with ⟨e, st⟩ | _ | _ <;> rfl

end

end generated.L1Bridgehub.L1Bridgehub
