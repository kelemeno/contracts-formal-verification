import Clear.ReasoningPrinciple


import generated.L1Bridgehub.L1Bridgehub.fun_transferOwnership_gen


/-
  Formal spec for the Yul translation of L1Bridgehub.transferOwnership, i.e. the
  OpenZeppelin Ownable / Ownable2Step ownership-transfer effect.

  Solidity semantics (Ownable._transferOwnership, as inlined by the Yul codegen):
      delete _pendingOwner;                 // _pendingOwner lives in slot 101
      address oldOwner = _owner;
      _owner = newOwner;                    // _owner lives in slot 51
      emit OwnershipTransferred(oldOwner, newOwner);

  Yul (see fun_transferOwnership_gen.lean):
      split_expr_0 := sload(101)
      split_expr_1 := shl(160, 2^96-1)              -- upper-96-bits mask (bits 160..255)
      split_expr_2 := and(split_expr_0, split_expr_1)
      sstore(101, split_expr_2)                     -- clear address bits of slot 101 (delete _pendingOwner)
      _1 := sload(51)                               -- old _owner word
      split_expr_3 := shl(160, 1)                   -- 2^160
      split_expr_4 := sub(split_expr_3, 1)          -- 2^160 - 1  (address mask)
      _2 := and(var_newOwner, split_expr_4)         -- address(newOwner)
      split_expr_5 := shl(160, 2^96-1)              -- upper-96-bits mask
      split_expr_6 := and(_1, split_expr_5)         -- old slot-51 upper bits
      split_expr_7 := or(split_expr_6, _2)          -- (old upper bits) | address(newOwner)
      sstore(51, split_expr_7)                      -- _owner := newOwner (address bits)   ← THE STORE
      ...log3 OwnershipTransferred(oldOwner, newOwner)...

  OWNERSHIP-TRANSFER INTEGRITY (this file):
  The decisive `sstore(51, split_expr_7)` is the LAST storage write of the function
  (only a `log3` follows), and it writes to the FIXED `_owner` slot 51 — the very
  slot that every `_checkOwner` / `onlyOwner` access-control guard reads (cf.
  fun_checkOwner_user.lean: `sload(51)`).  We therefore prove the END-OF-CALL
  property directly: in the final state s₉, the contract's `_owner` slot 51 holds,
  in its address bits, exactly `address(newOwner) = var_newOwner & (2^160-1)`:

      (s₉.evm.sload 51) &&& (2^160-1) = var_newOwner &&& (2^160-1)

  This is the faithful root-of-access-control guarantee: after `transferOwnership`,
  the owner address recognized by all subsequent owner checks is precisely the new
  owner that was requested.  (The upper 96 bits of slot 51 are dirty-bits that
  Solidity never reads as part of the address; the codegen preserves them, hence the
  mask on the left-hand side.)

  END-OF-CALL, not mid-execution: because slot 51 is a FIXED slot and is the final
  sstore, no later write can alias it, so no keccak-distinctness reasoning is needed.
-/

namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

set_option maxHeartbeats 4000000

-- The EVM address mask 2^160 - 1.
def transferOwnership_addrMask : UInt256 := Fin.shiftLeft (1 : UInt256) 160 - 1

-- `sstore σ slot v` makes `sload` at the SAME slot return `v` when `v ≠ 0`
-- (the EVM-model storage semantics: a zero write erases the key).
private lemma sload_sstore_same' (σ : EVM) (slot v : UInt256)
    (hv : v ≠ 0)
    (hown : (σ.lookupAccount σ.execution_env.code_owner).isSome) :
    (σ.sstore slot v).sload slot = v := by
  rcases hlk : σ.lookupAccount σ.execution_env.code_owner with _ | act
  · rw [hlk] at hown; simp at hown
  · unfold EVMState.sstore
    rw [hlk]
    unfold EVMState.sload EVMState.updateAccount EVMState.lookupAccount at *
    simp only []
    rw [Finmap.lookup_insert]
    unfold Account.updateStorage Account.lookupStorage
    simp only [beq_iff_eq, hv, if_neg, not_false_iff]
    rw [Finmap.lookup_insert]

@[simp] private lemma setEvm_Ok' (e : EVM) (evm : EVM) (store : VarStore) :
    State.setEvm e (Ok evm store) = Ok e store := rfl

@[simp] private lemma evm_Ok' (evm : EVM) (store : VarStore) :
    (Ok evm store).evm = evm := rfl

@[simp] private lemma evm_setEvm_insert' (e : EVM) (v : Identifier) (x : Literal) (s : State) :
    (State.setEvm e (State.insert v x s)).evm = (State.setEvm e s).evm := by
  unfold State.setEvm State.insert State.evm; rcases s <;> rfl

@[simp] private lemma setEvm_setEvm' (e e' : EVM) (s : State) :
    State.setEvm e (State.setEvm e' s) = State.setEvm e s := by
  unfold State.setEvm; rcases s <;> rfl

@[simp] private lemma isOk_multifill_eq (vars : List Identifier) (vals : List Literal)
    (s : State) : isOk (State.multifill vars vals s) = isOk s := by
  unfold State.multifill
  rcases s with ⟨e, st⟩ | _ | _ <;> simp only
  · -- multifill on Ok is a fold of inserts, each preserving Ok.
    generalize List.zip vars vals = ps
    induction ps with
    | nil => rfl
    | cons p rest ih => rw [List.foldr_cons, isOk_insert]; exact ih

@[simp] private lemma lookup_setEvm' (e : EVM) (v : Identifier) (s : State) :
    (s 🇪⟦e⟧)[v]!! = s[v]!! := by
  unfold State.setEvm State.lookup!; rcases s with ⟨e₀, st⟩ | _ | _ <;> rfl

-- `(s 🇪⟦e⟧).evm = e` when `s` is Ok; simp discharges `isOk s` via the lemmas above.
@[simp] private lemma evm_setEvm_of_ok (e : EVM) (s : State) (h : isOk s) :
    (s 🇪⟦e⟧).evm = e := by
  unfold State.setEvm State.evm isOk at *
  rcases s with ⟨e₀, st⟩ | _ | _ <;> simp_all

-- The end-of-call `match` (which keeps the computed evm and the caller's varstore)
-- has the same `evm` as the computed (revived) state, in every case.
private lemma match_evm' (X : State) (e₀ : EVM) (st₀ : VarStore) :
    (match 🧟X, Ok e₀ st₀ with
      | Ok e _, Ok _ st => Ok e st
      | s, _ => s).evm = (🧟X).evm := by
  cases 🧟X <;> rfl

-- `sstore` preserves the execution environment (it only touches account_map /
-- used_range), so it preserves the code owner.
private lemma execution_env_sstore' (σ : EVM) (a v : UInt256) :
    (σ.sstore a v).execution_env = σ.execution_env := by
  unfold EVMState.sstore
  rcases σ.lookupAccount σ.execution_env.code_owner with _ | act <;> rfl

-- `sstore` keeps the code-owner account present (it never deletes the account).
private lemma isSome_lookupAccount_sstore' (σ : EVM) (a v : UInt256)
    (hown : (σ.lookupAccount σ.execution_env.code_owner).isSome) :
    ((σ.sstore a v).lookupAccount (σ.sstore a v).execution_env.code_owner).isSome := by
  rw [execution_env_sstore']
  rcases hlk : σ.lookupAccount σ.execution_env.code_owner with _ | act
  · rw [hlk] at hown; simp at hown
  · unfold EVMState.sstore
    rw [hlk]
    unfold EVMState.lookupAccount EVMState.updateAccount at *
    simp only []
    rw [Finmap.lookup_insert]
    rfl

-- `sstore` at slot `a` leaves `sload` at a DIFFERENT slot `b` unchanged.
private lemma sload_sstore_diff' (σ : EVM) (a v b : UInt256) (hab : a ≠ b) :
    (σ.sstore a v).sload b = σ.sload b := by
  unfold EVMState.sstore
  rcases hlk : σ.lookupAccount σ.execution_env.code_owner with _ | act
  · rfl
  · unfold EVMState.sload EVMState.updateAccount EVMState.lookupAccount at *
    simp only []
    rw [Finmap.lookup_insert, hlk]
    unfold Account.updateStorage Account.lookupStorage
    by_cases hv : v = 0
    · subst hv; simp only [beq_self_eq_true, if_true]
      rw [Finmap.lookup_erase_ne (Ne.symm hab)]
    · simp only [beq_iff_eq, hv, if_neg, not_false_iff]
      rw [Finmap.lookup_insert_of_ne _ (Ne.symm hab)]

-- `Fin.lor a b ≠ 0` whenever `b ≠ 0` (any set bit of `b` survives in the disjunction).
private lemma lor_ne_zero_of_right_ne_zero (a b : UInt256) (hb : b ≠ 0) :
    Fin.lor a b ≠ 0 := by
  intro h
  apply hb
  apply Fin.ext
  -- `(Fin.lor a b).val = (a.val ||| b.val) % size`; the disjunction is `< size`, so the
  -- mod is the identity, and `a.val ||| b.val = 0` forces every bit of `b` clear.
  have hv0 : (a.val ||| b.val) % UInt256.size = 0 := congrArg Fin.val h
  have hlt : a.val ||| b.val < UInt256.size := by
    have h2 : a.val ||| b.val < 2 ^ 256 := Nat.or_lt_two_pow a.isLt b.isLt
    have : (2:Nat) ^ 256 = UInt256.size := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt] at hv0
  show b.val = 0
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (Nat.testBit · i) hv0
  simp only [Nat.testBit_or, Nat.zero_testBit, Bool.or_eq_false_iff] at this
  simp only [Nat.zero_testBit]
  exact this.2

-- Bit fact: masking with `2^160-1` keeps only the address bits.  The upper-bits
-- summand `land X (shiftLeft (2^96-1) 160)` (bits 160..255) is annihilated by the
-- address mask, and `land newOwner (2^160-1)` is unchanged by it.  Hence
--   (lor (land X upperMask) (land newOwner addrMask)) & addrMask = newOwner & addrMask.
private lemma bit_owner_mask (X newOwner : UInt256) :
    (Fin.lor (Fin.land X (Fin.shiftLeft 79228162514264337593543950335 160))
             (Fin.land newOwner (Fin.shiftLeft 1 160 - 1)))
      &&& transferOwnership_addrMask
      = newOwner &&& transferOwnership_addrMask := by
  show (Fin.lor (Fin.land X (Fin.shiftLeft 79228162514264337593543950335 160))
                (Fin.land newOwner (Fin.shiftLeft 1 160 - 1)))
        &&& (Fin.shiftLeft 1 160 - 1)
        = newOwner &&& (Fin.shiftLeft 1 160 - 1)
  have hand : ∀ a b : UInt256, a &&& b = Fin.land a b := fun _ _ => rfl
  have hlandv : ∀ a b : UInt256, (Fin.land a b).val = (a.val &&& b.val) % UInt256.size :=
    fun _ _ => rfl
  have hlorv : ∀ a b : UInt256, (Fin.lor a b).val = (a.val ||| b.val) % UInt256.size :=
    fun _ _ => rfl
  have hm1 : (Fin.shiftLeft (1:UInt256) 160 - 1).val = 2^160 - 1 := by decide
  have hm2 : (Fin.shiftLeft (79228162514264337593543950335:UInt256) 160).val
              = (2^96 - 1) <<< 160 := by decide
  have hsize : UInt256.size = 2^256 := by decide
  rw [hand, hand]
  apply Fin.ext
  simp only [hlandv, hlorv, hm1, hm2, hsize]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_or,
             Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft]
  by_cases hi2 : i < 160
  · have : ¬ (160 ≤ i) := by omega
    simp [hi2, this]
  · have hge : 160 ≤ i := by omega
    simp [hi2, hge]

def A_fun_transferOwnership (var_newOwner : Literal) (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    -- After the call, the contract's `_owner` slot 51 holds, in its address bits, the
    -- new owner's address: `(s₉.sload 51) & (2^160-1) = newOwner & (2^160-1)`.
    -- Hypotheses (the genuine ownership-transfer case): the new owner's address is
    -- non-zero, and the contract account exists.
    ((Fin.land var_newOwner transferOwnership_addrMask) ≠ 0 →
      (evm.lookupAccount evm.execution_env.code_owner).isSome →
      (s₉.evm.sload 51) &&& transferOwnership_addrMask
        = var_newOwner &&& transferOwnership_addrMask)

lemma fun_transferOwnership_abs_of_concrete {s₀ s₉ : State} { var_newOwner} :
  Spec (fun_transferOwnership_concrete_of_code.1  var_newOwner) s₀ s₉ →
  Spec (A_fun_transferOwnership  var_newOwner) s₀ s₉ := by
  unfold fun_transferOwnership_concrete_of_code A_fun_transferOwnership
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  intro evmA storeA hok
  cases hok
  intro hnz hown
  rw [← hconcrete]
  -- Fully evaluate the multifill/insert/setEvm plumbing: each `multifill` over an Ok
  -- state collapses to nested `insert`s, the whole computed state becomes a literal
  -- `Ok _ _`, `🧟` becomes the identity, the end-of-call `match` reduces, and the
  -- `.evm` projection peels down to the sstore stack; the var-store lookups resolve.
  rw [revive_of_ok (s := State.multifill _ _ _) (by
        repeat (first
          | exact isOk_Ok | apply isOk_multifill | rw [isOk_setEvm] | rw [isOk_insert]))]
  -- `split` on the end-of-call match yields the Ok arm (first) and the catch-all arm
  -- (second).  In the Ok arm the result is `Ok evm✝ store✝` with `evm✝` the computed
  -- evm; in the catch-all arm the result is the computed (revived) state directly.  In
  -- BOTH the `.evm` is the same `multifill … .evm`; we normalise each to that and run
  -- the identical finish.
  split
  · -- Ok arm: `h1 : multifill … = Ok evm✝ _`; rewrite `.evm` to the multifill's evm.
    rename_i _ _ _ _ _ h1 _
    simp only [evm_Ok']
    have h1' := congrArg State.evm h1
    simp only [evm_Ok'] at h1'
    rw [← h1']
    -- Phase 1: peel the multifill/setEvm/insert plumbing on the `.evm` path, exposing
    -- the sstore stack `(evm.sstore 101 _).sstore 51 _`.
    simp only [evm_multifill, setEvm_setEvm', evm_setEvm_insert', evm_setEvm_of_ok,
               setEvm_Ok', evm_Ok', evm_insert,
               isOk_multifill_eq, isOk_setEvm, isOk_insert, isOk_Ok]
    -- Phase 2: collapse the `multifill`s in the stored values into inserts (simp's
    -- discrimination tree declines `multifill_cons` on this giant term, but `rw`
    -- matches it syntactically), then read off the var-store lookups.
    repeat rw [multifill_cons]
    repeat rw [multifill_nil']
    simp (config := { decide := true }) only
      [lookup_setEvm', lookup_insert', lookup_insert, lookup_insert_of_ne,
       isOk_insert, isOk_Ok, isOk_setEvm]
    -- The end evm is `(evm.sstore 101 v101).sstore 51 V51`, with `51` the LAST write;
    -- read it back.  Abbreviate the two written words.
    set E := evm.sstore 101
              (Fin.land (evm.sload 101) (Fin.shiftLeft 79228162514264337593543950335 160))
      with hE
    set V51 := Fin.lor (Fin.land (E.sload 51)
                          (Fin.shiftLeft 79228162514264337593543950335 160))
                       (Fin.land var_newOwner (Fin.shiftLeft 1 160 - 1)) with hV
    -- `Fin.land var_newOwner addrMask` is the masked new-owner address, and it equals
    -- the `land newOwner (shiftLeft 1 160 - 1)` summand in `V51`.
    have haddr : Fin.land var_newOwner transferOwnership_addrMask
                  = Fin.land var_newOwner (Fin.shiftLeft 1 160 - 1) := rfl
    have hV51_ne : V51 ≠ 0 := by
      rw [hV]
      apply lor_ne_zero_of_right_ne_zero
      rw [← haddr]; exact hnz
    have hownE : (E.lookupAccount E.execution_env.code_owner).isSome :=
      isSome_lookupAccount_sstore' evm _ _ hown
    rw [sload_sstore_same' E 51 V51 hV51_ne hownE]
    -- Remaining: `V51 & addrMask = newOwner & addrMask`.  The upper-bits summand
    -- vanishes under the address mask; the masked-newOwner summand survives.
    rw [hV]
    exact bit_owner_mask _ var_newOwner
  · -- Catch-all arm: the goal already exposes `(multifill …).evm`; run the same finish.
    simp only [evm_multifill, setEvm_setEvm', evm_setEvm_insert', evm_setEvm_of_ok,
               setEvm_Ok', evm_Ok', evm_insert,
               isOk_multifill_eq, isOk_setEvm, isOk_insert, isOk_Ok]
    repeat rw [multifill_cons]
    repeat rw [multifill_nil']
    simp (config := { decide := true }) only
      [lookup_setEvm', lookup_insert', lookup_insert, lookup_insert_of_ne,
       isOk_insert, isOk_Ok, isOk_setEvm]
    set E := evm.sstore 101
              (Fin.land (evm.sload 101) (Fin.shiftLeft 79228162514264337593543950335 160))
      with hE
    set V51 := Fin.lor (Fin.land (E.sload 51)
                          (Fin.shiftLeft 79228162514264337593543950335 160))
                       (Fin.land var_newOwner (Fin.shiftLeft 1 160 - 1)) with hV
    have haddr : Fin.land var_newOwner transferOwnership_addrMask
                  = Fin.land var_newOwner (Fin.shiftLeft 1 160 - 1) := rfl
    have hV51_ne : V51 ≠ 0 := by
      rw [hV]; apply lor_ne_zero_of_right_ne_zero; rw [← haddr]; exact hnz
    have hownE : (E.lookupAccount E.execution_env.code_owner).isSome :=
      isSome_lookupAccount_sstore' evm _ _ hown
    rw [sload_sstore_same' E 51 V51 hV51_ne hownE]
    rw [hV]
    exact bit_owner_mask _ var_newOwner

end

end generated.L1Bridgehub.L1Bridgehub
