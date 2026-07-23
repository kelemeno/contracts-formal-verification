import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_leaf_storage_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_walk_discharge_user

/-
  THE VERIFIED MARK (L2InteropHandler, `fun_verifyBundle`'s tail).

  Once BOTH gates of `fun_verifyBundle` have passed — the sender anchor
  (`verify_sender_pass`, the proof's masked `message.sender` must be the
  InteropCenter built-in) and the inclusion verdict
  (`inclusion_verified_pass`, the `proveL2MessageInclusionShared` staticcall
  must decode `true`) — the function's tail records the outcome: it writes
  `BundleStatus.Verified (1)` into the low byte of `bundleStatus[bundleHash]`
  at the protocol-standard mapping slot `keccak256(bundleHash ‖ 1)`, and emits
  the `BundleVerified` event.  Quoted verbatim from the generated body
  (`fun_verifyBundle_gen.lean`, the three statements after the
  `MessageVerificationFailed` guard):

      {
          mstore(0, var_bundleHash)
          mstore(32, 1)
          let dataSlot := keccak256(0, 64)
          let cleaned_3 := 0
          cleaned_3 := 0
      }
      {
          let split_expr_46 := sload(dataSlot)
          let split_expr_47 := not(255)
          let split_expr_48 := and(split_expr_46, split_expr_47)
          let split_expr_49 := or(split_expr_48, 1)
          sstore(dataSlot, split_expr_49)
      }
      {log2(0, 0, <BundleVerified topic>, var_bundleHash)}

  This file proves:

  * `verify_mark_slot_block` — the slot staging is one `accOut` step at
    `(bundleHash, 1)`: the SAME slot the FullyExecuted mark writes and
    `fun_getBundleData` reads (`no_double_delivery_user.lean`, #50);
  * `verify_mark_write_block` — the write stores `(old &&& ~255) ||| 1`
    at that slot;
  * `verify_event_block` — the event emission leaves the state untouched
    (logs are observational in the model): the status write is the LAST
    state change of `fun_verifyBundle`;
  * `fin_mask_one` / `verified_status_reads_one` — pure readback: re-reading
    the slot after the write, the way `fun_getBundleData` does
    (`and(sload(slot), 0xff)`), returns exactly `Verified = 1`;
  * `read_after_verify_one` — the cross-evm composite: a later reader evm
    that agrees on the scratch junk window, carries the writer's keccak cache
    entry, and saw no intervening write to the status slot re-reads `1`.

  WHY IT MATTERS (bundle status machine, spec point 2): together with #50
  this closes the write surface of the status byte — `verifyBundle` writes
  `1`, `executeBundle`'s mark writes `2`, and the status guard accepts
  exactly `{0, 1}`.  `read_after_verify_one`'s value is exactly the `hs`
  premise of `status_verified_pass` (`no_double_delivery_user.lean`), so a
  verified bundle is ACCEPTED by the execute-path status guard (delivery
  liveness: verification cannot strand a bundle), while after execution the
  same machinery (`read_after_mark_two` + `status_blocked`) rejects it —
  verified-then-executed, each at most once.

  Caveats: the composition into the full `fun_verifyBundle` body sits behind
  the staticcall boundary (#38/#51 doctrine — the model cannot drive past a
  successful external call), so the tail is stated over its verbatim
  statement blocks; slot preservation between mark and re-read is the
  explicit `hpre` hypothesis, as in #50.

  Axiom-free.
-/

namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-! ### Local state-plumbing helpers -/

@[simp] private lemma insert_Ok {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

private lemma evm_Ok {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

private lemma setEvm_Ok {e E : EVMState} {σ : VarStore} :
    (Ok e σ).setEvm E = Ok E σ := rfl

private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok]; exact lookup_insert_of_ne h

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

private lemma primCall_keccakOut {s : State} {a b : Literal} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (keccakOut s.evm a b).2, [(keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

/-! ### The compiled pieces, quoted verbatim -/

/-- The status-slot computation of `fun_verifyBundle`'s tail:
`keccak256(bundleHash ‖ 1)` — the `bundleStatus` mapping slot. -/
private def verifyMarkBlk1 : Stmt := <s
  {
    mstore(0, var_bundleHash)
    mstore(32, 1)
    let dataSlot := keccak256(0, 64)
    let cleaned_3 := 0
    cleaned_3 := 0
}
>

/-- The status write of `fun_verifyBundle`'s tail, split lets per the
generator: `sstore(dataSlot, (old &&& ~255) ||| 1)`. -/
private def verifyMarkBlk2 : Stmt := <s
  {
    let split_expr_46 := sload(dataSlot)
    let split_expr_47 := not(255)
    let split_expr_48 := and(split_expr_46, split_expr_47)
    let split_expr_49 := or(split_expr_48, 1)
    sstore(dataSlot, split_expr_49)
}
>

/-- The `BundleVerified` event emission closing `fun_verifyBundle`'s body. -/
private def verifyEventBlk : Stmt := <s
  {log2(0, 0, 21352221386425818545601264208838403983447351590391855342993447920273378610260, var_bundleHash)}
>

/-! ### Closed forms of the mark -/

/-- **Slot block closed form**: the status slot is one `accOut` step at
`(bundleHash, 1)` — the same protocol-standard mapping slot as the
FullyExecuted mark and the `fun_getBundleData` status read (#50). -/
lemma verify_mark_slot_block
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {bh : Literal}
    (hbh : (Ok evm store)["var_bundleHash"]!! = bh) :
    exec (fuel+1) verifyMarkBlk1 (Ok evm store)
      = Ok (accOut evm bh 1).2
          (((store.insert "dataSlot" (accOut evm bh 1).1).insert
              "cleaned_3" 0).insert "cleaned_3" 0) := by
  unfold verifyMarkBlk1
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall', LetEq', Assign',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', eval, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMstore']
  simp only [multifill_cons, multifill_nil]
  simp only [evm_insert, evm_Ok, setEvm_Ok, insert_Ok]
  try simp only [List.head!]
  rw [hbh]
  rw [primCall_keccakOut]
  simp only [multifill_cons, multifill_nil, evm_Ok, setEvm_Ok, insert_Ok]
  have halign : keccakOut ((evm.mstore 0 bh).mstore 32 1) 0 64 = accOut evm bh 1 := by
    unfold accOut
    rfl
  try rw [halign]
  try simp only [halign]
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]

/-- **Write block closed form**: the tail stores `(old &&& ~255) ||| 1` —
`BundleStatus.Verified` in the low byte, everything else preserved — at the
status slot. -/
lemma verify_mark_write_block
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {d : Literal}
    (hd : (Ok evm store)["dataSlot"]!! = d) :
    exec (fuel+1) verifyMarkBlk2 (Ok evm store)
      = Ok (evm.sstore d (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 1))
          ((((store.insert "split_expr_46" (evm.sload d)).insert
              "split_expr_47" (Clear.UInt256.lnot 255)).insert
              "split_expr_48" (Fin.land (evm.sload d) (Clear.UInt256.lnot 255))).insert
              "split_expr_49" (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 1)) := by
  unfold verifyMarkBlk2
  -- let split_expr_46 := sload(dataSlot)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMSload', evm_Ok, insert_Ok]
  try simp only [List.head!]
  rw [hd]
  -- let split_expr_47 := not(255)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMNot', insert_Ok]
  -- let split_expr_48 := and(split_expr_46, split_expr_47)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMAnd', insert_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  -- let split_expr_49 := or(split_expr_48, 1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMOr', insert_Ok]
  rw [lookup_insert_self_fin]
  -- sstore(dataSlot, split_expr_49)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMSstore', evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hd]
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]

/-- **Event block closed form**: `log2` is observational in the model — the
event emission leaves the state untouched.  The status write is therefore
the LAST state change of `fun_verifyBundle`. -/
lemma verify_event_block
    {evm : EVMState} {store : VarStore} {fuel : ℕ} :
    exec (fuel+1) verifyEventBlk (Ok evm store) = Ok evm store := by
  unfold verifyEventBlk
  simp only [cons, nil]
  rw [ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMLog2']

/-! ### The low-byte mask: the stored status is exactly `Verified = 1` -/

private lemma low_bit_zero (n i : ℕ) (hi : i < 8) (h : n % 256 = 0) : n.testBit i = false := by
  rw [Nat.testBit_to_div_mod]
  have h256 : (256:ℕ) = 2^8 := by norm_num
  have hdvd : 2^(i+1) ∣ n := by
    have : (2:ℕ)^8 ∣ n := by rw [← h256]; exact Nat.dvd_of_mod_eq_zero h
    exact dvd_trans (pow_dvd_pow 2 (by omega)) this
  obtain ⟨k, rfl⟩ := hdvd
  have hpi : (0:ℕ) < 2^i := Nat.pos_pow_of_pos i (by norm_num)
  have : 2^(i+1) * k / 2^i = 2 * k := by
    rw [pow_succ]
    calc 2^i * 2 * k / 2^i = 2^i * (2*k) / 2^i := by ring_nf
    _ = 2*k := Nat.mul_div_cancel_left _ hpi
  rw [this]; simp [Nat.mul_mod_right]

private lemma tb255_lt (i : ℕ) (hge : 8 ≤ i) : (255:ℕ).testBit i = false :=
  Nat.testBit_lt_two_pow (by calc (255:ℕ) < 2^8 := by norm_num
    _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) hge)

/-- **Pure low-byte lemma.** The written status word `(x &&& ~255) ||| 1`
has low byte exactly `1 = BundleStatus.Verified`. -/
theorem fin_mask_one (x : UInt256) :
    Fin.land (Fin.lor (Fin.land x (Clear.UInt256.lnot 255)) 1) 255 = 1 := by
  apply Fin.ext
  rcases x with ⟨a, _⟩
  show Nat.land (Nat.lor (Nat.land a (UInt256.size - 256) % UInt256.size) 1 % UInt256.size) 255 % UInt256.size = 1
  have hsz : UInt256.size = 2^256 := by norm_num
  rw [hsz]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have key : ∀ z : ℕ, (z % 2^256).testBit i = z.testBit i := fun z => by
      rw [Nat.testBit_mod_two_pow]; simp [show i < 256 by omega]
    rw [key]
    show ((Nat.lor (Nat.land a (2^256 - 256) % 2^256) 1 % 2^256) &&& 255).testBit i = (1:ℕ).testBit i
    rw [show ∀ p q : ℕ, Nat.land p q = p &&& q from fun _ _ => rfl,
        show ∀ p q : ℕ, Nat.lor p q = p ||| q from fun _ _ => rfl]
    rw [Nat.testBit_land]
    rw [key ((a &&& (2^256 - 256)) % 2^256 ||| 1)]
    rw [Nat.testBit_lor]
    rw [key (a &&& (2^256 - 256))]
    rw [Nat.testBit_land]
    have hbmask : (2^256 - 256 : ℕ).testBit i = false := by
      apply low_bit_zero _ i hi; decide
    rw [hbmask, Bool.and_false, Bool.false_or, Bool.and_comm]
    have hb255 : (255:ℕ).testBit i = true := by interval_cases i <;> rfl
    rw [hb255, Bool.true_and]
  · have hge : 8 ≤ i := by omega
    have key : (Nat.land (Nat.lor (Nat.land a (2^256-256) % 2^256) 1 % 2^256) 255 % 2^256).testBit i = false := by
      rw [Nat.testBit_mod_two_pow]
      by_cases hi256 : i < 256
      · simp only [hi256, decide_True, Bool.true_and]
        show ((Nat.lor (Nat.land a (2^256-256) % 2^256) 1 % 2^256) &&& 255).testBit i = false
        rw [Nat.testBit_land, tb255_lt i hge, Bool.and_false]
      · simp [hi256]
    rw [key]
    have hb1 : (1:ℕ).testBit i = false :=
      Nat.testBit_lt_two_pow (by calc (1:ℕ) < 2^8 := by norm_num
        _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) hge)
    rw [hb1]

/-! ### The readback: after the mark, the status reads Verified -/

/-- **VERIFIED READS BACK (leg-level).**  After `fun_verifyBundle`'s status
write, re-reading the status slot the way `fun_getBundleData` does —
`and(sload(slot), 0xff)` — returns exactly `1 = Verified`.  This is the
value the execute-path status guard ACCEPTS (`status_verified_pass`, #50):
verification cannot strand a bundle. -/
theorem verified_status_reads_one
    {evm : EVMState} {d : UInt256}
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome) :
    Fin.land
      ((evm.sstore d (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 1)).sload d)
      255 = 1 := by
  rw [generated.L2InteropCommitmentTree.L2InteropCommitmentTree.sload_sstore_self hacc]
  exact fin_mask_one (evm.sload d)

/-- **RE-READ AFTER THE VERIFY MARK IS `Verified`.**  The cross-evm
composite, mirroring #50's `read_after_mark_two`: the reader's slot equals
the writer's slot (`accOut_deterministic` — junk-window frame, cache
transport, writer cleanliness), the reader's keccak step leaves storage
alone (`sload_accOut_of_clean`), nothing wrote the status slot in between
(`hpre`), and the pure readback gives `1`.  The conclusion is exactly the
`hs` premise of `status_verified_pass` (#50): a bundle marked Verified by
`fun_verifyBundle` PASSES the `executeBundle` status guard — the liveness
half of the bundle status machine. -/
theorem read_after_verify_one
    {evmW evmR : EVMState} {bh : UInt256}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i evmW.machine_state.memory
        = Finmap.lookup i evmR.machine_state.memory)
    (hmono : ∀ w : UInt256,
      Finmap.lookup (accInterval evmW bh 1) (accOut evmW bh 1).2.keccak_map = some w →
        Finmap.lookup (accInterval evmW bh 1) evmR.keccak_map = some w)
    (hcleanW : (accOut evmW bh 1).2.hash_collision = false)
    (hcleanR : (accOut evmR bh 1).2.hash_collision = false)
    (hacc : ((accOut evmW bh 1).2.lookupAccount
        (accOut evmW bh 1).2.execution_env.code_owner).isSome)
    (hpre : evmR.sload (accOut evmW bh 1).1
      = ((accOut evmW bh 1).2.sstore (accOut evmW bh 1).1
          (Fin.lor (Fin.land ((accOut evmW bh 1).2.sload (accOut evmW bh 1).1)
            (Clear.UInt256.lnot 255)) 1)).sload (accOut evmW bh 1).1) :
    Fin.land ((accOut evmR bh 1).2.sload (accOut evmR bh 1).1) 255 = 1 := by
  have hslot : (accOut evmR bh 1).1 = (accOut evmW bh 1).1 :=
    accOut_deterministic hframe hmono hcleanW
  rw [generated.L2InteropCommitmentTree.L2InteropCommitmentTree.sload_accOut_of_clean
      _ hcleanR, hslot, hpre]
  exact verified_status_reads_one hacc

end

end generated.L2InteropHandler.L2InteropHandler
