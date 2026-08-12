/-
  THE TRUST LEDGER, MACHINE-CHECKED.

  Run this file to reproduce the axiom audit of every headline security result:

      lake env lean specs/AttackVectors/Audit.lean

  It is NOT imported by anything and proves nothing itself; it exists so the trust
  claims made across the corpus can be checked in one command instead of trusted from
  prose.  `#print axioms` is the authority here, not `grep -L sorry` — roughly 98% of
  this repo's "completed" block specs are `A := concrete` aliases that remove the
  `sorry` token while proving nothing, so token counts mislead badly.

  RESULT as of this commit — 186 of 196 depend only on Lean's standard base
  (`propext`, `Quot.sound`, `Classical.choice`).  Reproduce the split with
  `scripts/audit-count.sh`, which PARSES the axiom sets rather than grepping for a
  literal list: `#print axioms` emits them in an unspecified order and wraps long
  lines, and both have caused miscounts here.  The 10 non-clean results are exactly
  the documented keccak idealizations — three storage-frame routes and the deep
  concrete insert chain.  The `_of_sound_start` variants are
  the GENERALIZED capstones: they replace the genesis hypothesis with soundness of the
  initial state, so they apply to a tree already in service or carried across an
  invariant-preserving upgrade — the form a migrated deployment needs, since such a
  tree cannot establish a genesis equation.

      CLEAN   no_theft                                    abstract capstone
      CLEAN   imt_no_theft                                deployed insert path
      CLEAN   imt_no_theft_in_contract_terms              same, contract vocabulary
      CLEAN   committed_member_gap_impossible_of_history   AFM x IMT composition
      CLEAN   leafSetOf_sstore_frame                      generic leaf-set frame
      AXIOMS  leafSetOf_arrWrite                          keccak256_add_ne_lowSlot,
                                                          keccak256_slot_sep
      CLEAN   mem_of_rootOf_eq                            root binding, kernel
      CLEAN   foldRoot_eq_rootOf                          root binding, piece (2)
      CLEAN   no_false_inclusion                          Merkle path soundness
      CLEAN   mixed_outcomes_permitted                    flow-atomicity LIMIT
      CLEAN   monotone_timestamps_indispensable           sharpness
      CLEAN   weak_window_without_dedup_breaks_keyInj     sharpness
      CLEAN   deadline_gate_indispensable                 sharpness
      CLEAN   capacity_overflow_forges_root               sharpness
      CLEAN   resetHistory_not_evolution                  governance-excepted
      CLEAN   unauthorized_sender_reverts                 InteropHandler gate
      CLEAN   authorized_passes                           InteropHandler gate
      CLEAN   verify_path_marks_bundle_verified           InteropHandler effect
      CLEAN   refunded_leg_cannot_refund_again            AFM no-double-refund
      CLEAN   timeout_implies_never_finalized             both timeout branches
      CLEAN   abiEncode_inj                               no collision below keccak
      CLEAN   packedPair_not_inj                          sharpness (encoding)
      CLEAN   no_duplicate_leg                            neighbour scan lifts
      CLEAN   neighbour_distinct_insufficient             sharpness (ordering)
      CLEAN   polarity_summary                            inclusion vs absence
      CLEAN   inclusion_binding_requires_honesty          sharpness (polarity)
      CLEAN   local_honest_insertion                      HonestInsertion located
      CLEAN   stranding_is_terminal                       recovery LIMIT
      CLEAN   revert_anywhere_blocks                      recovery LIMIT
      CLEAN   end_branch_with_begin_root_unsound          sharpness (root role)
      CLEAN   last_of_rightEmpty                          discharges hlast (index level)
      CLEAN   end_branch_from_onchain_check               end branch, check to conclusion
      CLEAN   begin_branch_needs_beginIsPrevEnd           sharpness (begin(N)=end(N-1))
      CLEAN   routes_exclusive                            no double delivery via 2 routes
      CLEAN   callReach_from_executed                     each call delivered at most once
      CLEAN   atomic_source_bound                         atomic path: declared = vouching chain

  READ THE CLEAN MARKS CORRECTLY.  Axiom-clean means the PROOF adds nothing to Lean's
  base — it does NOT mean the result is unconditional.  Most of these carry
  hypotheses that the concrete layer must discharge, and several deliberately do so:
  `mem_of_rootOf_eq` assumes node-hash pair-injectivity (standing in for keccak
  collision resistance); `imt_no_theft` assumes `ConcreteLeafHistory`, which when
  discharged via `leafSetOf_evolution_step` pulls in four keccak idealizations;
  `foldRoot_eq_rootOf` assumes a pure pair-hash and a fixed sibling stream.  Each
  file's header states its own obligations.  The three `sharpness` entries are
  counterexamples — they prove a hypothesis is LOAD-BEARING, not that the system is
  safe.  `mixed_outcomes_permitted` records a LIMIT: per-leg outcomes may differ.
-/
import specs.AttackVectors.NoTheft
import specs.AttackVectors.ConcreteBridge
import specs.AttackVectors.CrossContract
import specs.AttackVectors.LeafSetFrame
import specs.AttackVectors.RootBinding
import specs.AttackVectors.RootForgery
import specs.AttackVectors.FlowAtomicity
import specs.AttackVectors.Timestamps
import specs.AttackVectors.InsertGuard
import specs.AttackVectors.StaleSnapshot
import specs.AttackVectors.TreeShape
import specs.AttackVectors.ResetAndZero
import specs.FoldWalkBridge
import specs.CachedHash
import specs.LeafHashWindow
import specs.FoldCacheInv
import specs.CachedHashInj
import specs.RootBindingCached
import specs.AttackVectors.RootBindingFull
import specs.LeafHashBridge
import specs.AttackVectors.CommittedRoot
import specs.AttackVectors.LeafHashList
import specs.MerkleProofSound
import specs.KeccakFresh
import specs.KeccakLowSlot
import specs.KeccakSlotSep
import specs.KeccakSeqInj
import specs.ForgeryFresh
import specs.FoldFresh
import specs.FoldRightPeel
import specs.FoldForced
import specs.FoldFuel
import specs.FoldCacheInj
import specs.FoldDescent
import specs.FoldIndexBridge
import specs.TreeFoldPins
import specs.AttackVectors.FoldMembership
import specs.AttackVectors.WitnessMember
import specs.AttackVectors.NoDoubleSpend
import specs.AttackVectors.NoCrossBundle
import specs.AttackVectors.NoCrossLeg
import specs.AttackVectors.NestedSlots
import specs.AttackVectors.CapacityInvariant
import specs.AttackVectors.TimeoutSoundness
import specs.AttackVectors.NoReplayCross
import specs.L1Bridgehub.L1Bridgehub.fun_registerNewZKChain_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_weld_user
import specs.MerkleSpec
import specs.AttackVectors.LeafDecode3
import specs.InteropHandler.Layout
import specs.AtomicFlowManager.Layout
import specs.AttackVectors.BundleHashEncoding
import specs.AttackVectors.FlowCanonical
import specs.AttackVectors.ProofPolarity
import specs.AttackVectors.LocalHonesty
import specs.AttackVectors.RecoveryLimits
import specs.AttackVectors.LastBatchInRoot
import specs.AttackVectors.BundleStatusMachine
import specs.AttackVectors.AtomicSourceBinding

#print axioms AttackVectors.NoTheft.no_theft
#print axioms AttackVectors.NoTheft.no_theft_of_sound_start
#print axioms AttackVectors.ConcreteBridge.imt_no_theft
#print axioms AttackVectors.ConcreteBridge.imt_no_theft_of_sound_start
#print axioms AttackVectors.ConcreteBridge.imt_no_theft_in_contract_terms
#print axioms AttackVectors.CrossContract.committed_member_gap_impossible_of_history
#print axioms AttackVectors.CrossContract.committed_member_gap_impossible_of_sound_start
#print axioms AttackVectors.LeafSetFrame.leafSetOf_sstore_frame
#print axioms AttackVectors.LeafSetFrame.leafSetOf_vtiWrite
#print axioms AttackVectors.LeafSetFrame.leafSetOf_vtiWrite_of_config
#print axioms AttackVectors.LeafSetFrame.leafSetOf_lowSlotWrite
#print axioms AttackVectors.LeafSetFrame.leafSetOf_lowSlotWrite_of_config
#print axioms AttackVectors.LeafSetFrame.leafSetOf_arrWrite
#print axioms AttackVectors.RootBinding.mem_of_rootOf_eq
#print axioms AttackVectors.LeafDecode3.root_binding
#print axioms MerkleSpec.rootOf_inj_of_h_inj'
#print axioms Clear.FoldWalkBridge.foldRoot_eq_rootOf
#print axioms Clear.FoldWalkBridge.foldRoot_eq_rootOf_of_inv
#print axioms Clear.FoldWalkBridge.foldRoot_eq_rootOf_of_levelInv
#print axioms Clear.FoldWalkBridge.foldRoot_eq_rootOf_of_pathInv
#print axioms Clear.FoldWalkBridge.foldRoot_eq_rootOf_of_stepInv
#print axioms Clear.FoldCacheInv.foldRoot_eq_rootOf_cached
#print axioms Clear.FoldCacheInv.foldRoot_eq_rootOf_cached_self
#print axioms Clear.FinBits.shiftLeft_five_val
#print axioms Clear.CachedHash.accOut_eq_hashOf
#print axioms Clear.LeafHashWindow.leafInterval_inj
#print axioms Clear.LeafHashWindow.leafHashOf_inj
#print axioms Clear.CachedHashInj.accInterval_inj
#print axioms Clear.CachedHashInj.hashOf_pair_inj
#print axioms Clear.MerkleCachedInj.rootOf_inj_on
#print axioms Clear.RootBindingCached.rootOf_inj_cached
#print axioms Clear.RootBindingCached.getD_of_rootOf_eq_cached
#print axioms AttackVectors.RootBindingFull.root_binding_fully_cached
#print axioms AttackVectors.RootBindingFull.not_placeable_of_not_mem
#print axioms Clear.LeafHashBridge.hashLeafOut_eq_leafHashOut
#print axioms Clear.LeafHashBridge.keccakOut_val_congr
#print axioms AttackVectors.CommittedRoot.committed_root_is_treeRoot
#print axioms AttackVectors.CommittedRoot.committed_roots_agree
#print axioms AttackVectors.CommittedRoot.committedLeafAt_of_zero
#print axioms AttackVectors.CommittedRoot.committed_leafhash_is_cached
#print axioms AttackVectors.CommittedRoot.committed_leafhash_in_fold_state
#print axioms AttackVectors.LeafHashList.root_binding_from_storage
#print axioms Clear.MerkleProofSound.walk_pins_leaf_and_sibs
#print axioms Clear.MerkleProofSound.walk_accept_pins_leaf_free_sibs
#print axioms Clear.MerkleProofSound.no_forged_walk
#print axioms Clear.KeccakFresh.cacheInUsed_keccakOut
#print axioms Clear.KeccakFresh.keccakOut_miss_fresh
#print axioms Clear.KeccakFresh.cacheInUsed_accOut
#print axioms Clear.KeccakFresh.cacheInj_keccakOut
#print axioms Clear.KeccakLowSlot.keccakOut_ne_lowSlot
#print axioms Clear.KeccakLowSlot.noLowCached_keccakOut
#print axioms Clear.KeccakSlotSep.keccakOut_add_ne_slot
#print axioms Clear.KeccakSlotSep.separated_keccakOut
#print axioms Clear.KeccakLowSlot.keccak256_ne_lowSlot_of_config
#print axioms Clear.KeccakSlotSep.keccak256_slot_sep_of_config
#print axioms Clear.KeccakLowSlot.keccak256_add_ne_lowSlot_of_config
#print axioms Clear.KeccakLowSlot.cachedInWindow_keccakOut
#print axioms AttackVectors.LeafSetFrame.leafCount_arrWrite_of_config
#print axioms Clear.KeccakSlotSep.cached_off_ne_off
#print axioms Clear.KeccakSlotSep.cached_off_ne_off_of_len_ne
#print axioms Clear.KeccakSlotSep.arr_write_frames_mapping
#print axioms Clear.KeccakSeqInj.keccakOut_seq_ne
#print axioms Clear.KeccakSeqInj.clean_keccakOut
#print axioms Clear.KeccakSeqInj.sload_sstore_of_cached_ne
#print axioms Clear.KeccakSeqInj.sload_sstore_of_seq_ne
#print axioms AttackVectors.LeafSetFrame.leafSetOf_arrWrite_of_config
#print axioms Clear.FoldCacheInj.cacheInj_foldRoot
#print axioms Clear.FoldDescent.fold_descent
#print axioms Clear.FoldDescent.no_forged_fold
#print axioms Clear.FoldIndexBridge.idxAt_val
#print axioms Clear.FoldIndexBridge.idxAt_parity
#print axioms Clear.TreeFoldPins.tree_fold_pins_leaf
#print axioms Clear.TreeFoldPins.fold_accept_pins_leaf
#print axioms Clear.TreeFoldPins.fold_rejects_wrong_leaf
#print axioms AttackVectors.FoldMembership.fold_accept_implies_member
#print axioms AttackVectors.FoldMembership.fold_rejects_non_member
#print axioms AttackVectors.WitnessMember.witness_leaf_member
#print axioms AttackVectors.WitnessMember.witness_non_member_rejects
#print axioms AttackVectors.WitnessMember.committedLeafAt_of_committedAtIn
#print axioms AttackVectors.WitnessMember.habs_of_committedAtIn
#print axioms AttackVectors.WitnessMember.gap_impossible_of_committedAtIn
#print axioms AttackVectors.NoDoubleSpend.no_delivery_and_reclaim
#print axioms AttackVectors.NoDoubleSpend.no_delivery_and_reclaim_from_genesis
#print axioms AttackVectors.NoCrossBundle.status_write_frames_other_bundle
#print axioms AttackVectors.NoCrossBundle.status_survives_other_writes
#print axioms AttackVectors.NoCrossBundle.status_write_frames_fresh_bundle
#print axioms AttackVectors.NoCrossBundle.slot_ne_of_ne
#print axioms AttackVectors.NoCrossBundle.write_frames_other_mapping
#print axioms AttackVectors.NoCrossLeg.leg_slot_ne
#print axioms AttackVectors.NoCrossLeg.legState_frames_other_leg
#print axioms AttackVectors.NoCrossLeg.legState_frames_fresh_leg
#print axioms AttackVectors.NoCrossLeg.legState_survives_refund_loop
#print axioms AttackVectors.NoCrossLeg.leg_slot_ne_of_flow_ne
#print axioms AttackVectors.NoCrossLeg.flow_substituted_claim_reverts
#print axioms AttackVectors.NestedSlots.triple_slot_ne
#print axioms AttackVectors.NestedSlots.nestedSlot_inj
#print axioms AttackVectors.NestedSlots.nested_write_frames
#print axioms AttackVectors.NestedSlots.fresh_nestedSlot_ne_cached
#print axioms AttackVectors.NestedSlots.nested_write_frames_fresh
#print axioms AttackVectors.CapacityInvariant.cap_push
#print axioms AttackVectors.CapacityInvariant.cap_at_size
#print axioms AttackVectors.TimeoutSoundness.begin_absence_implies_never_finalized
#print axioms AttackVectors.TimeoutSoundness.finalized_blocks_begin_timeout
#print axioms AttackVectors.NoReplayCross.replay_still_reverts_after_other_finalization
#print axioms generated.L1Bridgehub.L1Bridgehub.fun_registerNewZKChain_value_survives_fun_add
#print axioms AttackVectors.NestedSlots.finalize_frames_other_batch
#print axioms AttackVectors.NoCrossLeg.legState_frames_same_bundle_other_flow
#print axioms generated.L2InteropCommitmentTree.L2InteropCommitmentTree.insertGlue_leafSetOf
#print axioms generated.L2InteropCommitmentTree.L2InteropCommitmentTree.leafSetOf_evolution_step
#print axioms generated.L2InteropCommitmentTree.L2InteropCommitmentTree.insertGlue_evolution
#print axioms generated.L2InteropCommitmentTree.L2InteropCommitmentTree.insertGlue_evolution_step
#print axioms generated.L2InteropCommitmentTree.L2InteropCommitmentTree.leafSetOf_imtInsert
#print axioms generated.L2InteropCommitmentTree.L2InteropCommitmentTree.root_pins_written_leaf
#print axioms Clear.ForgeryFresh.accOut_args_forced
#print axioms Clear.ForgeryFresh.accOut_ne_of_args_ne
#print axioms Clear.FoldFresh.cacheInUsed_foldRoot
#print axioms Clear.FoldFresh.foldRoot_lookup_mono
#print axioms Clear.FoldFresh.foldRoot_mload_high
#print axioms Clear.FoldFresh.foldRoot_junk_window
#print axioms Clear.FoldFresh.foldRoot_builder_entry
#print axioms Clear.FoldRightPeel.foldRoot_succ_right
#print axioms Clear.FoldRightPeel.foldRoot_last_step_accOut
#print axioms Clear.FoldForced.foldRoot_top_args_forced
#print axioms Clear.FoldForced.foldRoot_top_ne
#print axioms Clear.KeccakFuel.Fuel.keccakOut
#print axioms Clear.FoldFuel.fuel_foldRoot
#print axioms Clear.FoldFuel.fuel_nonempty_at_depth
#print axioms AttackVectors.LeafHashList.leafHashList_hleaves
#print axioms Clear.LeafHashWindow.leafHashOut_eq_leafHashOf_frame
#print axioms Clear.LeafHashWindow.leafHashOut_eq_leafHashOf_shift
#print axioms Clear.LeafHashWindow.leafInterval_eq_of_tail_agree
#print axioms Clear.LeafHashWindow.leafInterval_shift
#print axioms AttackVectors.LeafDecode3.lh3_inj_on_cached
#print axioms AttackVectors.LeafDecode3.root_binding_cached
#print axioms AttackVectors.RootForgery.no_false_inclusion
#print axioms AttackVectors.FlowAtomicity.mixed_outcomes_permitted
#print axioms AttackVectors.Timestamps.monotone_timestamps_indispensable
#print axioms AttackVectors.InsertGuard.weak_window_without_dedup_breaks_keyInj
#print axioms AttackVectors.StaleSnapshot.deadline_gate_indispensable
#print axioms AttackVectors.TreeShape.capacity_overflow_forges_root
#print axioms AttackVectors.ResetAndZero.resetHistory_not_evolution
#print axioms InteropHandler.Layout.unauthorized_sender_reverts
#print axioms InteropHandler.Layout.authorized_passes
#print axioms InteropHandler.Layout.verify_path_marks_bundle_verified
#print axioms InteropHandler.Layout.statusOf_frames_other_bundle
#print axioms InteropHandler.Layout.status_read_binds_statusOf
#print axioms InteropHandler.Layout.unverified_stays_unverified
#print axioms AtomicFlowManager.Layout.refunded_leg_cannot_refund_again

-- Timeout protocol: the END branch (the BEGIN branch is listed above)
#print axioms AttackVectors.TimeoutSoundness.end_absence_implies_never_finalized
#print axioms AttackVectors.TimeoutSoundness.end_absence_implies_never_finalized'
#print axioms AttackVectors.TimeoutSoundness.finalized_blocks_end_timeout
#print axioms AttackVectors.TimeoutSoundness.timeout_implies_never_finalized

-- Encoding: no collision below keccak in the bundle-hash derivation
#print axioms AttackVectors.BundleHashEncoding.fromBytesBE_toBytesBE
#print axioms AttackVectors.BundleHashEncoding.abiDecode_abiEncode
#print axioms AttackVectors.BundleHashEncoding.abiEncode_inj
#print axioms AttackVectors.BundleHashEncoding.packed_inj
#print axioms AttackVectors.BundleHashEncoding.packedPair_not_inj

-- Flow canonicality: the neighbour scan lifts to global claims
#print axioms AttackVectors.FlowCanonical.ascending_iff_pairwise
#print axioms AttackVectors.FlowCanonical.no_duplicate_leg
#print axioms AttackVectors.FlowCanonical.ascending_unique
#print axioms AttackVectors.FlowCanonical.valid_pairing_functional
#print axioms AttackVectors.FlowCanonical.valid_unique_per_leg_set
#print axioms AttackVectors.FlowCanonical.neighbour_distinct_insufficient

-- Proof polarity: inclusion self-binds, absence cannot
#print axioms AttackVectors.ProofPolarity.inclusion_self_binds
#print axioms AttackVectors.ProofPolarity.absence_at_every_wrong_chain
#print axioms AttackVectors.ProofPolarity.finalized_leg_still_absent_elsewhere
#print axioms AttackVectors.ProofPolarity.refund_blocked_when_chain_pinned
#print axioms AttackVectors.ProofPolarity.inclusion_binding_requires_honesty
#print axioms AttackVectors.ProofPolarity.polarity_summary

-- Where HonestInsertion lives: enforced locally, "same code" globally
#print axioms AttackVectors.LocalHonesty.local_honest_insertion
#print axioms AttackVectors.LocalHonesty.honestInsertion_of_guards_everywhere

-- Timeout recovery: the exact shape of "best-effort" (LIMITS, not safety claims)
#print axioms AttackVectors.RecoveryLimits.partial_recovery_accepted
#print axioms AttackVectors.RecoveryLimits.accepted_below_full_recovery
#print axioms AttackVectors.RecoveryLimits.stranding_is_terminal
#print axioms AttackVectors.RecoveryLimits.one_revert_blocks_all
#print axioms AttackVectors.RecoveryLimits.revert_anywhere_blocks
#print axioms AttackVectors.RecoveryLimits.retry_does_not_help

-- Timeout protocol: the begin/end roots are not interchangeable
#print axioms AttackVectors.TimeoutSoundness.begin_branch_with_end_root_sound
#print axioms AttackVectors.TimeoutSoundness.end_branch_with_begin_root_unsound

-- "Last batch in root": the zero-cascade check IS "last filled leaf"
#print axioms AttackVectors.LastBatchInRoot.exists_first_left
#print axioms AttackVectors.LastBatchInRoot.last_of_rightEmpty
#print axioms AttackVectors.LastBatchInRoot.rightEmpty_of_last
#print axioms AttackVectors.LastBatchInRoot.hlast_of_last_in_root
#print axioms AttackVectors.LastBatchInRoot.end_branch_from_onchain_check
#print axioms AttackVectors.TimeoutSoundness.begin_absence_of_beginIsPrevEnd
#print axioms AttackVectors.TimeoutSoundness.begin_branch_needs_beginIsPrevEnd

-- Bundle status machine: one delivery per bundle, two mutually exclusive routes
#print axioms AttackVectors.BundleStatusMachine.reach_from_fullyExecuted
#print axioms AttackVectors.BundleStatusMachine.reach_from_unbundled
#print axioms AttackVectors.BundleStatusMachine.routes_exclusive
#print axioms AttackVectors.BundleStatusMachine.both_routes_available
#print axioms AttackVectors.BundleStatusMachine.callReach_from_executed
#print axioms AttackVectors.BundleStatusMachine.callReach_from_cancelled
#print axioms AttackVectors.BundleStatusMachine.call_outcomes_exclusive
#print axioms AttackVectors.BundleStatusMachine.cancel_idempotent_execute_not

-- The atomic path's source binding, and what it rests on
#print axioms AttackVectors.AtomicSourceBinding.atomic_source_bound
#print axioms AttackVectors.AtomicSourceBinding.atomic_source_unbound_without_honest
