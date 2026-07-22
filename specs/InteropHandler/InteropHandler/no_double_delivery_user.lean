import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_leaf_storage_user

/-
  NO DOUBLE DELIVERY — the executed-once state machine, leg one.

  `InteropHandler._markFullyExecutedAndRun` sets
  `bundleStatus[bundleHash] := FullyExecuted (= 2)` BEFORE running any of the
  bundle's calls (CEI), at the mapping slot `keccak256(bundleHash ‖ 1)` — the
  same `accOut` slot shape as everything else in the protocol.  This file
  proves the SET side and its readback, mirroring #22's no-double-refund:

  * `mark_slot_block` / `mark_write_block` — closed forms of the two compiled
    prologue blocks: the status slot is `(accOut evm bh 1).1`, and the write
    stores `(old &&& ~255) ||| 2` there;
  * `fin_mask_two` — the written word's low byte is exactly `2`
    (`BundleStatus.FullyExecuted`), and it is nonzero;
  * `delivered_status_reads_two` — re-reading the slot after the write gives
    status `2`: the `executeBundle`/`receive` path's status check (which
    accepts only `Unreceived`/`Verified`, read in `fun_getBundleData` as
    `and(sload(slot), 0xff)`) REJECTS a re-delivery.

  A bundle executes at most once — the delivery-side mirror of #22.

  Axiom-free.
-/

namespace generated.InteropHandler.InteropHandler

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

private lemma lookup_ok_evm {σ : VarStore} {k : Identifier} (e e' : EVMState) :
    (Ok e σ)[k]!! = (Ok e' σ)[k]!! := rfl

private lemma primCall_keccakOut {s : State} {a b : Literal} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (keccakOut s.evm a b).2, [(keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

/-! ### The two compiled prologue blocks, quoted verbatim -/

/-- The status-slot computation: `keccak256(bundleHash ‖ 1)`. -/
private def markBlk1 : Stmt := <s
  {
    mstore(0, var_bundleHash)
    mstore(32, 1)
    let dataSlot := keccak256(0, 64)
    let cleaned := 0
    cleaned := 0
}
>

/-- The status write: `sstore(slot, (old &&& ~255) ||| 2)`. -/
private def markBlk2 : Stmt := <s
  {
    let split_expr_0 := sload(dataSlot)
    let split_expr_1 := not(255)
    let split_expr_2 := and(split_expr_0, split_expr_1)
    let split_expr_3 := or(split_expr_2, 2)
    sstore(dataSlot, split_expr_3)
}
>

/-- **Block 1 closed form**: the status slot is one `accOut` step at
`(bundleHash, 1)` — the protocol-standard mapping slot. -/
lemma mark_slot_block
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {bh : Literal}
    (hbh : (Ok evm store)["var_bundleHash"]!! = bh) :
    exec (fuel+1) markBlk1 (Ok evm store)
      = Ok (accOut evm bh 1).2
          (((store.insert "dataSlot" (accOut evm bh 1).1).insert
              "cleaned" 0).insert "cleaned" 0) := by
  unfold markBlk1
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall', LetEq', Assign',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', eval, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMstore']
  simp only [multifill_cons, multifill_nil]
  rw [hbh]
  simp only [evm_insert, evm_Ok, setEvm_Ok, insert_Ok]
  rw [primCall_keccakOut]
  simp only [multifill_cons, multifill_nil, evm_Ok, setEvm_Ok, insert_Ok]
  have halign : keccakOut ((evm.mstore 0 bh).mstore 32 1) 0 64 = accOut evm bh 1 := by
    unfold accOut
    rfl
  try rw [halign]
  try simp only [halign]
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]

/-- **Block 2 closed form**: the write stores `(old &&& ~255) ||| 2` at the
status slot. -/
lemma mark_write_block
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {d : Literal}
    (hd : (Ok evm store)["dataSlot"]!! = d) :
    exec (fuel+1) markBlk2 (Ok evm store)
      = Ok (evm.sstore d (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 2))
          ((((store.insert "split_expr_0" (evm.sload d)).insert
              "split_expr_1" (Clear.UInt256.lnot 255)).insert
              "split_expr_2" (Fin.land (evm.sload d) (Clear.UInt256.lnot 255))).insert
              "split_expr_3" (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 2)) := by
  unfold markBlk2
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMSload', EVMNot', EVMAnd', EVMOr', EVMSstore']
  simp only [multifill_cons, multifill_nil]
  rw [hd]
  simp only [evm_insert, evm_Ok, setEvm_Ok, insert_Ok]
  simp only [lookup_insert_self_fin]
  have n1 : (Ok evm (Finmap.insert "split_expr_1" (Clear.UInt256.lnot 255)
      (Finmap.insert "split_expr_0" (evm.sload d) store)))["split_expr_0"]!!
      = evm.sload d := by
    rw [lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  simp only [n1]
  try simp only [lookup_insert_self_fin]
  have n2 : (Ok evm (Finmap.insert "split_expr_3"
      (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 2)
      (Finmap.insert "split_expr_2" (Fin.land (evm.sload d) (Clear.UInt256.lnot 255))
        (Finmap.insert "split_expr_1" (Clear.UInt256.lnot 255)
          (Finmap.insert "split_expr_0" (evm.sload d) store)))))["dataSlot"]!! = d := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact hd
  simp only [n2]
  try simp only [lookup_insert_self_fin]
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]

/-! ### The low-byte mask: the stored status is exactly `FullyExecuted = 2` -/

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

/-- **Pure low-byte lemma.** The written status word `(x &&& ~255) ||| 2`
has low byte exactly `2 = BundleStatus.FullyExecuted`. -/
theorem fin_mask_two (x : UInt256) :
    Fin.land (Fin.lor (Fin.land x (Clear.UInt256.lnot 255)) 2) 255 = 2 := by
  apply Fin.ext
  rcases x with ⟨a, _⟩
  show Nat.land (Nat.lor (Nat.land a (UInt256.size - 256) % UInt256.size) 2 % UInt256.size) 255 % UInt256.size = 2
  have hsz : UInt256.size = 2^256 := by norm_num
  rw [hsz]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have key : ∀ z : ℕ, (z % 2^256).testBit i = z.testBit i := fun z => by
      rw [Nat.testBit_mod_two_pow]; simp [show i < 256 by omega]
    rw [key]
    show ((Nat.lor (Nat.land a (2^256 - 256) % 2^256) 2 % 2^256) &&& 255).testBit i = (2:ℕ).testBit i
    rw [show ∀ p q : ℕ, Nat.land p q = p &&& q from fun _ _ => rfl,
        show ∀ p q : ℕ, Nat.lor p q = p ||| q from fun _ _ => rfl]
    rw [Nat.testBit_land]
    rw [key ((a &&& (2^256 - 256)) % 2^256 ||| 2)]
    rw [Nat.testBit_lor]
    rw [key (a &&& (2^256 - 256))]
    rw [Nat.testBit_land]
    have hbmask : (2^256 - 256 : ℕ).testBit i = false := by
      apply low_bit_zero _ i hi; decide
    rw [hbmask, Bool.and_false, Bool.false_or, Bool.and_comm]
    have hb255 : (255:ℕ).testBit i = true := by interval_cases i <;> rfl
    rw [hb255, Bool.true_and]
  · have hge : 8 ≤ i := by omega
    have key : (Nat.land (Nat.lor (Nat.land a (2^256-256) % 2^256) 2 % 2^256) 255 % 2^256).testBit i = false := by
      rw [Nat.testBit_mod_two_pow]
      by_cases hi256 : i < 256
      · simp only [hi256, decide_True, Bool.true_and]
        show ((Nat.lor (Nat.land a (2^256-256) % 2^256) 2 % 2^256) &&& 255).testBit i = false
        rw [Nat.testBit_land, tb255_lt i hge, Bool.and_false]
      · simp [hi256]
    rw [key]
    have hb2 : (2:ℕ).testBit i = false :=
      Nat.testBit_lt_two_pow (by calc (2:ℕ) < 2^8 := by norm_num
        _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) hge)
    rw [hb2]

/-- The written status word is nonzero (its low byte is `2`). -/
theorem fin_mask_two_ne_zero (x : UInt256) :
    Fin.lor (Fin.land x (Clear.UInt256.lnot 255)) 2 ≠ 0 := by
  intro h
  have := fin_mask_two x
  rw [h] at this
  simp only [Fin.land] at this
  exact absurd this (by decide)

/-! ### The readback: after the mark, the status reads FullyExecuted -/

/-- **NO DOUBLE DELIVERY (leg-level).**  After `_markFullyExecutedAndRun`'s
status write, re-reading the status slot the way `fun_getBundleData` does —
`and(sload(slot), 0xff)` — returns exactly `2 = FullyExecuted`.  The
execute/receive paths accept only `Unreceived`/`Verified`, so a second
delivery of the same bundle is REJECTED by its own first write (which lands
BEFORE any bundle call runs — CEI). -/
theorem delivered_status_reads_two
    {evm : EVMState} {d : UInt256}
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome) :
    Fin.land
      ((evm.sstore d (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 2)).sload d)
      255 = 2 := by
  rw [generated.L2InteropCommitmentTree.L2InteropCommitmentTree.sload_sstore_self hacc]
  exact fin_mask_two (evm.sload d)

end

end generated.InteropHandler.InteropHandler
