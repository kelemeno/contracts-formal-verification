/-
  THE TRUST LEDGER, MACHINE-CHECKED.

  Run this file to reproduce the axiom audit of every headline security result:

      lake env lean specs/AttackVectors/Audit.lean

  It is NOT imported by anything and proves nothing itself; it exists so the trust
  claims made across the corpus can be checked in one command instead of trusted from
  prose.  `#print axioms` is the authority here, not `grep -L sorry` — roughly 98% of
  this repo's "completed" block specs are `A := concrete` aliases that remove the
  `sorry` token while proving nothing, so token counts mislead badly.

  RESULT as of this commit — 73 of 74 depend only on Lean's standard base
  (`propext`, `Quot.sound`, `Classical.choice`).  The `_of_sound_start` variants are
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
import specs.ForgeryFresh
import specs.FoldFresh
import specs.FoldRightPeel
import specs.FoldForced
import specs.FoldFuel
import specs.MerkleSpec
import specs.AttackVectors.LeafDecode3
import specs.InteropHandler.Layout
import specs.AtomicFlowManager.Layout

#print axioms AttackVectors.NoTheft.no_theft
#print axioms AttackVectors.NoTheft.no_theft_of_sound_start
#print axioms AttackVectors.ConcreteBridge.imt_no_theft
#print axioms AttackVectors.ConcreteBridge.imt_no_theft_of_sound_start
#print axioms AttackVectors.ConcreteBridge.imt_no_theft_in_contract_terms
#print axioms AttackVectors.CrossContract.committed_member_gap_impossible_of_history
#print axioms AttackVectors.CrossContract.committed_member_gap_impossible_of_sound_start
#print axioms AttackVectors.LeafSetFrame.leafSetOf_sstore_frame
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
#print axioms AttackVectors.LeafHashList.root_binding_from_storage
#print axioms Clear.MerkleProofSound.walk_pins_leaf_and_sibs
#print axioms Clear.MerkleProofSound.walk_accept_pins_leaf_free_sibs
#print axioms Clear.MerkleProofSound.no_forged_walk
#print axioms Clear.KeccakFresh.cacheInUsed_keccakOut
#print axioms Clear.KeccakFresh.keccakOut_miss_fresh
#print axioms Clear.KeccakFresh.cacheInUsed_accOut
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
#print axioms AtomicFlowManager.Layout.refunded_leg_cannot_refund_again
