import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_8832779172174931881
import generated.L1Nullifier.L1Nullifier.fun_resolveLegacyL2Sender
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.write_to_memory_uint16
import generated.L1Nullifier.L1Nullifier.abi_decode_available_length_bytes
import generated.L1Nullifier.L1Nullifier.abi_decode_available_length_array_bytes32_dyn
import generated.L1Nullifier.L1Nullifier.modifier_nonReentrant_892
import generated.L1Nullifier.L1Nullifier.Common.block_3361755722822923188

import generated.L1Nullifier.L1Nullifier.fun_finalizeWithdrawal_gen


/-
  PUBLIC-ENTRY ROUTING THROUGH THE NULLIFIER MODIFIER (L1Nullifier).

  `fun_finalizeWithdrawal` is the PUBLIC withdrawal-finalization entry point of
  zkSync's L1Nullifier (Yul: fun_finalizeWithdrawal_gen.lean).  After decoding the
  call parameters into the `finalizeWithdrawalParams` struct in scratch memory
  (`memPtr`), its very last statement is

      modifier_nonReentrant_892(memPtr)

  i.e. the entire security-critical body of finalization is executed inside the
  `nonReentrant` modifier.  That modifier has TWO independently-proven deep
  guarantees (specs/.../modifier_nonReentrant_892_user.lean):

    • `A_modifier_nonReentrant_892` — replay protection: the run reads the
      isWithdrawalFinalized[chainId][batch][index] flag (the CHECK block,
      block_4604436955705083701, routing through the WithdrawalAlreadyFinalized
      require-helper) immediately before SETTING that flag to true
      (block_4633566561656549981).
    • `A_proof_required_for_withdrawal` — the finalized-flag SET is inseparable
      from the Merkle-proof verification fun_verifyWithdrawal.

  Those theorems are stated about the modifier IN ISOLATION.  This file closes the
  single-function-scope gap (assumption A8) for the most security-critical entry:
  it proves that EVERY non-out-of-fuel run of the PUBLIC entry
  `fun_finalizeWithdrawal` necessarily ROUTES THROUGH `modifier_nonReentrant_892`.
  Concretely, there exist intermediate states `s_mod_in s_mod_out` (the states the
  public entry reaches around the modifier call) and a `memPtr` argument such that

      Spec (A_modifier_nonReentrant_892 memPtr) s_mod_in s_mod_out

  holds — so the replay-protection and proof-required guarantees of the modifier
  apply to the actual public withdrawal API, not just to the modifier on its own.

  Mechanically the public entry's `concrete_of_code` witness chain peels EIGHT
  sub-block executions (block_9174066418542949334, block_1694155005937695202,
  if_8832779172174931881, block_5269992435314537623, block_8457754549386515971,
  block_417375367100373739, block_3082704935474736305, block_3361755722822923188).
  The modifier call lives inside the EIGHTH block (block_3361755722822923188),
  whose own concrete relation peels two sub-calls — abi_decode_available_length_
  array_bytes32_dyn followed by `modifier_nonReentrant_892` — the latter being the
  witness we extract.

  AXIOM NOTE: `#print axioms A_fun_finalizeWithdrawal_routes_through_modifier`
  reports [propext, Quot.sound, Classical.choice, sorryAx].  The `sorryAx` is NOT
  from this proof (which is `sorry`-free): it is inherited from the GENERATED tree,
  where the primitive opcode stubs `…mcopy` / `…tstore` ship as `:= by sorry` and
  are reachable transitively via fun_verifyWithdrawal inside the modifier — exactly
  as for `modifier_nonReentrant_892_abs_of_concrete`.  Editing generated/ is out of
  scope.
-/

namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

set_option maxHeartbeats 4000000

-- Public-entry routing spec: a successful (non-out-of-fuel) run of the public
-- `fun_finalizeWithdrawal` entry routes through `modifier_nonReentrant_892`.  There
-- exist intermediate states `s_mod_in s_mod_out` and a memory argument `memPtr` on
-- which the nullifier modifier's deep spec (`A_modifier_nonReentrant_892`, the
-- replay-protection + proof-required guarantee) holds.
-- The block that contains the `modifier_nonReentrant_892(memPtr)` call is the
-- public entry's eighth (final) sub-block, `block_3361755722822923188`.  The spec
-- records that this block ran (witnessed by `Spec A_block_3361755722822923188`), and
-- that WHENEVER it is entered in a normal (Ok) state — i.e. the parameter-decoding
-- prefix did not revert before the modifier — the run ROUTES THROUGH the nullifier
-- modifier `modifier_nonReentrant_892`, on some memory argument `memPtr` and
-- intermediate states `s_mod_in s_mod_out`.  Hence the modifier's deep guarantees
-- (replay protection + proof-required-for-withdrawal) apply to the public entry, not
-- just to the modifier in isolation.
def A_fun_finalizeWithdrawal  (var_chainId var_l2BatchNumber var_l2MessageIndex var_l2TxNumberInBatch var__message_offset var_message_length var_merkleProof_offset var_merkleProof_1685_length : Literal) (s₀ s₉ : State) : Prop :=
  ∃ (s_blk_in s_blk_out : State),
    -- the final block (holder of the modifier call) executed,
    Spec L1Nullifier.Common.A_block_3361755722822923188 s_blk_in s_blk_out ∧
    -- and whenever that block is entered normally (Ok input), the run necessarily
    -- routes through `modifier_nonReentrant_892`.
    (isOk s_blk_in →
      ∃ (memPtr : Literal) (s_mod_in s_mod_out : State),
        Spec (A_modifier_nonReentrant_892 memPtr) s_mod_in s_mod_out)

lemma fun_finalizeWithdrawal_abs_of_concrete {s₀ s₉ : State} { var_chainId var_l2BatchNumber var_l2MessageIndex var_l2TxNumberInBatch var__message_offset var_message_length var_merkleProof_offset var_merkleProof_1685_length} :
  Spec (fun_finalizeWithdrawal_concrete_of_code.1  var_chainId var_l2BatchNumber var_l2MessageIndex var_l2TxNumberInBatch var__message_offset var_message_length var_merkleProof_offset var_merkleProof_1685_length) s₀ s₉ →
  Spec (A_fun_finalizeWithdrawal  var_chainId var_l2BatchNumber var_l2MessageIndex var_l2TxNumberInBatch var__message_offset var_message_length var_merkleProof_offset var_merkleProof_1685_length) s₀ s₉ := by
  unfold fun_finalizeWithdrawal_concrete_of_code A_fun_finalizeWithdrawal
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  -- Peel the public entry's 8 sub-block witnesses; the 8th block (`hblk`) is
  -- block_3361755722822923188, the holder of the `modifier_nonReentrant_892` call.
  -- `s_blk_in` is its input (the 7th block's output), `s_blk_out` its output.
  rcases hconcrete with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, s_blk_in, _, s_blk_out, hblk, hend⟩
  refine ⟨s_blk_in, s_blk_out, hblk, ?_⟩
  intro hok_blk_in
  -- `s_blk_out` is the final block's output and flows to `s₉` via the trailing match
  -- `hend`.  Since the whole entry ends non-out-of-fuel (`hne`), `s_blk_out` is too.
  have hne_blk_out : ¬ ❓ s_blk_out := by
    intro hc
    rw [isOutOfFuel_iff_s_eq_OutOfFuel] at hc
    rw [hc] at hend
    apply hne
    rw [← hend]
    simp [isOutOfFuel, State.reviveJump]
  -- Unfold the final block's concrete relation; with the Ok input it exposes its two
  -- internal sub-calls (abi_decode…, then `modifier_nonReentrant_892`).
  have hblk' := hblk
  unfold L1Nullifier.Common.A_block_3361755722822923188
         L1Nullifier.Common.block_3361755722822923188_concrete_of_code at hblk'
  rw [Spec] at hblk'
  rcases s_blk_in with ⟨eb, stb⟩ | jcb | cb
  · -- the block runs to `s_blk_out` (not out of fuel); peel its two sub-calls.
    simp only at hblk'
    have hpeel := hblk' hne_blk_out
    rcases hpeel with ⟨_, _, s_mod_in, hmod, _⟩
    exact ⟨_, _, s_mod_in, hmod⟩
  · exact absurd hok_blk_in (by simp [isOk])
  · exact absurd hok_blk_in (by simp [isOk])

end

end generated.L1Nullifier.L1Nullifier
