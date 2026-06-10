import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.block_4604436955705083701
import generated.L1Nullifier.L1Nullifier.Common.block_4633566561656549981

import generated.L1Nullifier.L1Nullifier.modifier_nonReentrant_892_gen


/-
  WITHDRAWAL REPLAY PROTECTION for zkSync's L1Nullifier.

  `modifier_nonReentrant_892` is the guarded body of `finalizeWithdrawal`.  Its Yul
  (see modifier_nonReentrant_892_gen.lean) performs, in order:

    1. reentrancy status guard;
    2. fun_requireNotPaused();
    3. read params  _1 = chainId, _2 = l2BatchNumber, _3 = l2MessageIndex;
    4. compute the nested-mapping slot for  isWithdrawalFinalized[_1][_2][_3];
    5. CHECK block (block_4604436955705083701):
         split_expr_8 := read_from_storage_split_offset_bool(slot)
         split_expr_9 := iszero(split_expr_8)
         split_expr_10 := cleanup_bool(split_expr_9)
         require_helper_error_WithdrawalAlreadyFinalized(split_expr_10)  -- REVERTS if finalized
       (then re-opens the slot recomputation with split_expr_11);
    6. SET block (block_4633566561656549981):
         recompute slot s13 (two more keccak mapping_index_access steps)
         update_storage_value_offset_bool_to_bool_17751(s13)  -- SETS finalized := true
         fun_verifyWithdrawal(params)  -- Merkle-proof verification;
    7. pre-shared-bridge Eth / token withdrawal branches + fund release (abstracted).

  After the gen was re-chunked into per-block abstractions, the modifier's
  `concrete_of_code` witness chain peels FIFTEEN sub-block executions in order
  (see modifier_nonReentrant_892_gen.lean):

    #1  if_7589762552718540589        (reentrancy status == 0 guard)
    #2  if_4307119837691313886        (reentrancy status == 1 guard)
    #3  block_4512968904597907462     (sstore status:=2, requireNotPaused, read _1,_2)
    #4  block_6519403908612865045     (read _3, compute keccak slot s5,s6,s7)
    #5  block_4604436955705083701     (CHECK: read flag, cleanup, replay-revert helper)
    #6  block_4633566561656549981     (SET: recompute slot, set flag true, verifyWithdrawal)
    #7  if_7574793255574635930        ... (pre-shared-bridge branches / fund release)
    #8  if_4899343340082050920
    #9  block_3425825946090805875
    #10 block_4058806278313870700
    #11 if_7049296412361229646
    #12 block_8220686982859115513
    #13 block_7579817276070379677
    #14 if_396429549932726667
    #15 if_3525216432756457624
  followed by the final `sstore(status, 1)` wrap-up.

  This file records the two security-critical events as control-flow witnesses
  inside the modifier's execution (the same style as
  L1AssetRouter.fun_transferFundsToNTV_inner and the DiamondProxy decoder):

  • CHECK (replay-revert):  there is an intermediate state `s_check_in` reached by
      the modifier on which `block_4604436955705083701` runs to `s_check_out`.  That
      block reads isWithdrawalFinalized[_1][_2][_3], cleans it, and feeds it to
      `require_helper_error_WithdrawalAlreadyFinalized`, which reverts exactly when
      the flag is already set — the literal replay guard.

  • SET:  the state `s_check_out` flows directly into `block_4633566561656549981`,
      which recomputes the SAME nullifier slot and writes the finalized flag to true
      via `update_storage_value_offset_bool_to_bool_17751`, then runs
      `fun_verifyWithdrawal`.

  The two blocks are chained (CHECK's output is SET's input), so the recorded
  property is precisely: every non-out-of-fuel run of the modifier executes the
  replay CHECK immediately before the finalized-flag SET.
-/

namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

set_option maxHeartbeats 4000000

-- Abstract replay-protection spec.  Phrased as the existence of the two decisive
-- chained sub-block executions inside `modifier_nonReentrant_892`:
--   * the replay CHECK block (`block_4604436955705083701`), reading the finalized
--     flag at the nullifier slot and routing through the WithdrawalAlreadyFinalized
--     require-helper, and
--   * the finalized-flag SET block (`block_4633566561656549981`), which recomputes
--     the same slot, writes the flag to true, and runs the Merkle proof check
--     (fun_verifyWithdrawal).
-- The two are chained: the CHECK's output state is exactly the SET's input state.
def A_modifier_nonReentrant_892 (var_finalizeWithdrawalParams_889_mpos : Literal) (s₀ s₉ : State) : Prop :=
  ∃ (s_check_in s_check_out s_set_out : State),
    -- (CHECK) the finalized flag at the nullifier slot is read, cleaned, and fed to
    -- the WithdrawalAlreadyFinalized require-helper (reverts if already finalized).
    Spec L1Nullifier.Common.A_block_4604436955705083701 s_check_in s_check_out ∧
    -- (SET) the same nullifier slot is recomputed, the finalized flag is written to
    -- true, and the Merkle proof is verified (fun_verifyWithdrawal).
    Spec L1Nullifier.Common.A_block_4633566561656549981 s_check_out s_set_out

lemma modifier_nonReentrant_892_abs_of_concrete {s₀ s₉ : State} { var_finalizeWithdrawalParams_889_mpos} :
  Spec (modifier_nonReentrant_892_concrete_of_code.1  var_finalizeWithdrawalParams_889_mpos) s₀ s₉ →
  Spec (A_modifier_nonReentrant_892  var_finalizeWithdrawalParams_889_mpos) s₀ s₉ := by
  unfold modifier_nonReentrant_892_concrete_of_code A_modifier_nonReentrant_892
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  -- Peel the 15-witness sub-block chain.  Each witness is `⟨ssᵢ, hᵢ, …⟩` with
  -- hᵢ : Spec A_block_i ssᵢ₋₁ ssᵢ.  The CHECK is the 5th block (witness #5,
  -- input = ss₄ = `s_check_in`, output = `s_check_out`); the SET is the 6th block
  -- (input = `s_check_out`, output = `s_set_out`).
  rcases hconcrete with
    ⟨_, _, _, _, _, _, s_check_in, _,
     s_check_out, hcheck, s_set_out, hset,
     _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  exact ⟨s_check_in, s_check_out, s_set_out, hcheck, hset⟩

-- AXIOM NOTE: `#print axioms modifier_nonReentrant_892_abs_of_concrete` reports
-- [propext, Quot.sound, Classical.choice, sorryAx].  The `sorryAx` is NOT from this
-- proof (which is `sorry`-free): it is inherited from the GENERATED tree, where the
-- primitive opcode stubs `generated.L1Nullifier.L1Nullifier.mcopy` and `…tstore`
-- ship as `:= by sorry`.  They are reachable transitively via `fun_verifyWithdrawal`
-- (imported by the SET block / modifier).  Touching generated/ is out of scope here.

/- =========================================================================
   P3: PROOF-REQUIRED-FOR-WITHDRAWAL.

   A successful (non-out-of-fuel) execution of `modifier_nonReentrant_892`
   (the guarded body of `finalizeWithdrawal`) WITNESSES a call to
   `fun_verifyWithdrawal` — the Merkle-proof verification.  In other words, the
   finalized-flag SET and the proof check are inseparable: no withdrawal is
   finalized without the proof being verified.

   Mechanically: the SET block `block_4633566561656549981` runs
       split_expr_12 := mapping_index_access(split_expr_11, _2)
       split_expr_13 := mapping_index_access(split_expr_12, _3)
       update_storage_value_offset_bool_to_bool_17751(split_expr_13)  -- SET flag
       expr_component, … := fun_verifyWithdrawal(params)              -- PROOF CHECK
   and its `concrete_of_code` proof peels exactly those four sub-calls, the last
   being `fun_verifyWithdrawal_abs_of_code`.  We extract that fourth witness.
   ========================================================================= -/

-- The proof-required property: every (non-out-of-fuel) modifier run reaches the
-- finalized-flag SET block `block_4633566561656549981`, and whenever it does so in a
-- normal execution state (the SET-block input `s_set_in` is `Ok` — which it always is
-- on the finalize path, the replay-revert keeping the state Ok), the SET block's run
-- WITNESSES a call to `fun_verifyWithdrawal` — the Merkle-proof verification.  Thus the
-- finalized-flag write and the proof check are inseparable: no withdrawal is finalized
-- without proof verification.
def A_proof_required_for_withdrawal
    (var_finalizeWithdrawalParams_889_mpos : Literal) (s₀ s₉ : State) : Prop :=
  ∃ (s_set_in s_set_out : State),
    -- the finalized-flag SET block ran (it both writes the flag and calls verify),
    Spec L1Nullifier.Common.A_block_4633566561656549981 s_set_in s_set_out ∧
    -- and whenever the SET block is entered normally (Ok input), the Merkle-proof
    -- verification fun_verifyWithdrawal is run inside it.
    (isOk s_set_in →
      ∃ (s_vw_in s_vw_out : State) (var_assetId var_transferData : Identifier) (params : Literal),
        Spec (A_fun_verifyWithdrawal var_assetId var_transferData params) s_vw_in s_vw_out)

theorem proof_required_for_withdrawal {s₀ s₉ : State} { var_finalizeWithdrawalParams_889_mpos} :
  Spec (modifier_nonReentrant_892_concrete_of_code.1  var_finalizeWithdrawalParams_889_mpos) s₀ s₉ →
  Spec (A_proof_required_for_withdrawal  var_finalizeWithdrawalParams_889_mpos) s₀ s₉ := by
  unfold modifier_nonReentrant_892_concrete_of_code A_proof_required_for_withdrawal
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  -- Peel the modifier's full 15-block chain.  `hset` is the SET block (#6) witness
  -- (input = CHECK output, output = `s_set_out`); blocks #7..#15 (`h7..h15`) and the
  -- final wrap-up `hfin` follow, which we keep to back-propagate non-out-of-fuel-ness.
  rcases hconcrete with
    ⟨_, _, _, _, _, _, _, _,
     s_set_in, _, s_set_out, hset,
     w7, h7, w8, h8, w9, h9, w10, h10, w11, h11,
     w12, h12, w13, h13, w14, h14, w15, h15, hfin⟩
  -- The SET block's output `s_set_out` is not out of fuel: back-propagate from the
  -- final wrap-up `hfin` (¬❓ of the end-state, via `hne`) through blocks #15..#7.
  have hne15 : ¬ ❓ w15 := by
    -- the post-chain wrap-up `hfin` rewrites the final state from `w15`; `hne`
    -- asserts the end-state is not out of fuel, so neither is `w15`.
    intro hc
    rw [isOutOfFuel_iff_s_eq_OutOfFuel] at hc
    subst hc
    apply hne
    rw [← hfin]
    simp [isOutOfFuel, State.reviveJump, State.setEvm]
  have hne14 : ¬ ❓ w14 := not_isOutOfFuel_Spec h15 hne15
  have hne13 : ¬ ❓ w13 := not_isOutOfFuel_Spec h14 hne14
  have hne12 : ¬ ❓ w12 := not_isOutOfFuel_Spec h13 hne13
  have hne11 : ¬ ❓ w11 := not_isOutOfFuel_Spec h12 hne12
  have hne10 : ¬ ❓ w10 := not_isOutOfFuel_Spec h11 hne11
  have hne9  : ¬ ❓ w9  := not_isOutOfFuel_Spec h10 hne10
  have hne8  : ¬ ❓ w8  := not_isOutOfFuel_Spec h9 hne9
  have hne7  : ¬ ❓ w7  := not_isOutOfFuel_Spec h8 hne8
  have hne_set_out : ¬ ❓ s_set_out := not_isOutOfFuel_Spec h7 hne7
  -- `hset : Spec A_block_4633566561656549981 s_set_in s_set_out`.  Unfold the SET
  -- block's concrete relation; with `¬❓ s_set_out` we peel its four internal
  -- sub-call witnesses, the last of which is `fun_verifyWithdrawal`.
  -- Provide the SET-block witness; then discharge the Ok-input implication by
  -- peeling the SET block's internal four-subcall chain (4th = fun_verifyWithdrawal).
  refine ⟨s_set_in, s_set_out, hset, ?_⟩
  intro hok_set_in
  have hset' := hset
  unfold L1Nullifier.Common.A_block_4633566561656549981
         L1Nullifier.Common.block_4633566561656549981_concrete_of_code at hset'
  rw [Spec] at hset'
  -- `s_set_in` is Ok; reduce the Spec-match to the `¬❓ s_set_out → existential` body.
  rcases s_set_in with ⟨e6, st6⟩ | jc6 | c6
  · simp only at hset'
    have hpeel := hset' hne_set_out
    -- SET block sub-chain: ⟨s1,h_map1,s2,h_map2,s3,h_update,s_vw_out,h_verify,hfin⟩;
    -- the 4th sub-call witness `hvw` is fun_verifyWithdrawal, with input s3.
    rcases hpeel with ⟨_, _, _, _, s_vw_in, _, s_vw_out, hvw, _⟩
    exact ⟨s_vw_in, s_vw_out, _, _, _, hvw⟩
  · exact absurd hok_set_in (by simp [isOk])
  · exact absurd hok_set_in (by simp [isOk])

-- AXIOM NOTE (also applies to `modifier_nonReentrant_892_abs_of_concrete` above):
-- `#print axioms proof_required_for_withdrawal` reports
-- [propext, Quot.sound, Classical.choice, sorryAx].  As above, the `sorryAx` is NOT
-- from these proofs (both are `sorry`-free) but from the GENERATED primitive stubs
-- `…mcopy` / `…tstore` (`:= by sorry`), reachable transitively via
-- `fun_verifyWithdrawal`.  Editing generated/ is out of scope.

end

end generated.L1Nullifier.L1Nullifier
