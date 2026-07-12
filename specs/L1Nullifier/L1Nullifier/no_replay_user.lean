import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_9006375582650777893
import generated.L1Nullifier.L1Nullifier.Common.block_4604436955705083701

import generated.L1Nullifier.L1Nullifier.read_from_storage_split_offset_bool
import generated.L1Nullifier.L1Nullifier.cleanup_bool
import generated.L1Nullifier.L1Nullifier.require_helper_error_WithdrawalAlreadyFinalized
import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17749
import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256
import generated.L1Nullifier.L1Nullifier.update_storage_value_offset_bool_to_bool_17751_gen

import specs.RevertModel
import specs.KeccakDeterminism

/-
  CROSS-TRANSACTION WITHDRAWAL REPLAY PROTECTION for zkSync's L1Nullifier.

  This file proves the *genuine* anti-double-spend property, distinct from the
  per-call check-then-set already recorded as control-flow witnesses in
  `modifier_nonReentrant_892_user.lean`.

  Claim: a withdrawal whose persistent finalized flag is ALREADY set
  (isWithdrawalFinalized[chainId][l2BatchNumber][l2MessageIndex] ≠ 0) CANNOT be
  finalized again — re-running the replay-CHECK block of `finalizeWithdrawal` from
  such a storage state ends with `evm.reverted = true`.

  The mechanism, in the CHECK block `block_4604436955705083701`:
      split_expr_8  := read_from_storage_split_offset_bool(slot)   -- and(sload slot, 255)
      split_expr_9  := iszero(split_expr_8)
      split_expr_10 := cleanup_bool(split_expr_9)                  -- iszero(iszero …)
      require_helper_error_WithdrawalAlreadyFinalized(split_expr_10)  -- REVERTS iff arg = 0
  If the read flag byte is nonzero (slot already set) then
  split_expr_9 = 0, split_expr_10 = 0, and the require-helper reverts.

  We prove this with the `reverted` flag from `specs.RevertModel`.
-/

namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     L1Nullifier.Common generated.L1Nullifier L1Nullifier Clear.RevertModel

set_option maxRecDepth 6000
set_option maxHeartbeats 4000000

/-- `insert` on an `Ok` state writes into the underlying varstore. -/
@[simp] lemma insert_Ok {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

/-- `isOk` is invariant under `multifill` (iff form, usable by `simp`). -/
@[simp] lemma isOk_multifill_eq {s : State} {vars : List Identifier} {args : List Literal} :
    isOk (multifill vars args s) = isOk s := by
  rcases s with ⟨e, st⟩ | _ | _
  · rw [eq_true (isOk_multifill (by trivial)), eq_true (by trivial : isOk (Ok e st))]
  · unfold multifill; rfl
  · unfold multifill; rfl

/-- On an `Ok` state, `setEvm` overwrites the evm verbatim. -/
lemma evm_setEvm_of_isOk {s : State} {e : EVMState} (h : isOk s) :
    (s.setEvm e).evm = e := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

/-- `reviveJump` is the identity on `Ok` states. -/
lemma reviveJump_of_isOk {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

/-- `reviveJump` keeps the evm of an `Ok` state. -/
lemma evm_reviveJump_of_isOk {s : State} (h : isOk s) : (🧟 s).evm = s.evm := by
  rw [reviveJump_of_isOk h]

/-- The `require_helper` call (with argument `0`) leaves an `Ok`-shaped state whose
    evm has `reverted = true`: the body `if iszero(0){…revert(0,4)}` runs the revert,
    and the call wrappers (reviveJump/overwrite?/setStore) keep that reverting evm
    and restore the caller varstore.  This is the literal replay guard. -/
lemma require_call_isOk_and_reverted
    {evm : EVMState} {store : VarStore} {fuel : ℕ} :
    ∃ e : EVMState,
      execCall (fuel+1) require_helper_error_WithdrawalAlreadyFinalized []
          (Ok evm store, [0]) = Ok e store ∧ e.reverted = true := by
  unfold execCall call require_helper_error_WithdrawalAlreadyFinalized
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  -- The body is the single `if iszero(condition){…revert}`.  Replay it.
  rw [cons, nil, If']
  -- evaluate the guard `iszero(condition)`; condition was bound to 0 by initcall.
  simp only [evalArgs, head', reverse', multifill', PrimCall', Lit', Var',
             execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil,
             List.nil_append, List.singleton_append, evalTail, cons']
  rw [EVMIszero']
  simp only [head', List.head!]
  -- `condition` initcalls to 0, so `iszero 0 = 1 ≠ 0`: the body runs.
  rw [lookup_initcall_1]
  simp only [fromBool, decide_True, Bool.toUInt256, cond_true]
  rw [if_pos (by decide : ((if True then (1 : UInt256) else 0)) ≠ 0)]
  -- replay the body: shl, mstore, revert(0,4).
  simp only [cons, nil, ExprStmtPrimCall', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMShl', EVMMstore', EVMRevert', multifill_cons, multifill_nil]
  simp only [overwrite?_of_Ok, reviveJump]
  -- the post-body state is `setStore B (Ok evm store)` with `B` an Ok state whose
  -- evm is a fresh `evm_revert …` (reverted).  Abstract `B`'s pieces.
  rw [lookup_insert' (by apply isOk_initcall_of_isOk; trivial)]
  -- now `B = (insert split_expr_0 over initcall) |> setEvm (mstore …) |> setEvm (evm_revert …)`.
  generalize hX : (Ok evm store)☎️⟦["condition"], [0]⟧⟦"split_expr_0"↦Fin.shiftLeft 732062997 226⟧ = X
  have hX_ok : isOk X := by rw [← hX, isOk_insert]; apply isOk_initcall_of_isOk; trivial
  -- B = (X.setEvm (X.evm.mstore 0 (shl))).setEvm (… .evm_revert 0 4); it is Ok.
  have hB_ok : isOk ((X🇪⟦X.evm.mstore 0 (Fin.shiftLeft 732062997 226)⟧)
      🇪⟦(X🇪⟦X.evm.mstore 0 (Fin.shiftLeft 732062997 226)⟧).evm.evm_revert 0 4⟧) := by
    rw [isOk_setEvm, isOk_setEvm]; exact hX_ok
  obtain ⟨eB, sB, hBeq⟩ := State_of_isOk hB_ok
  refine ⟨eB, ?_, ?_⟩
  · rw [hBeq, setStore_ok]
  · -- B.evm = eB; and B's outer layer is `setEvm (evm_revert …)`, so reverted = true.
    have hBevm : eB = ((X🇪⟦X.evm.mstore 0 (Fin.shiftLeft 732062997 226)⟧)
        🇪⟦(X🇪⟦X.evm.mstore 0 (Fin.shiftLeft 732062997 226)⟧).evm.evm_revert 0 4⟧).evm := by
      rw [hBeq]; rfl
    rw [hBevm, evm_setEvm_of_isOk (by rw [isOk_setEvm]; exact hX_ok)]
    rfl

/-- The `require_helper` call (with argument `0`) REVERTS. -/
lemma require_helper_reverts_of_zero
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {s₉ : State}
    (hexec : execCall (fuel+1) require_helper_error_WithdrawalAlreadyFinalized []
                (Ok evm store, [0]) = s₉) :
    s₉.evm.reverted = true := by
  obtain ⟨e, heq, hr⟩ := require_call_isOk_and_reverted (evm := evm) (store := store) (fuel := fuel)
  rw [← hexec, heq]; exact hr

/-- The `require_helper` call leaves an `Ok`-shaped state. -/
lemma require_call_isOk
    {evm : EVMState} {store : VarStore} {fuel : ℕ} :
    isOk (execCall (fuel+1) require_helper_error_WithdrawalAlreadyFinalized []
            (Ok evm store, [0])) := by
  obtain ⟨e, heq, _⟩ := require_call_isOk_and_reverted (evm := evm) (store := store) (fuel := fuel)
  rw [heq]; trivial

/--
  Closed form for `read_from_storage_split_offset_bool(slot)`: the body is
  `let s0 := sload(slot); value := and(s0, 255)`, which only reads storage, so the
  call returns the caller state with the evm UNCHANGED and the single return
  variable `v` bound to `Fin.land (evm.sload slot) 255` (the low byte of the slot).
-/
lemma read_call_state
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slot : Literal} {v : Identifier} :
    execCall (fuel+1) read_from_storage_split_offset_bool [v]
        (Ok evm store, [slot])
      = (Ok evm store)⟦v ↦ Fin.land (evm.sload slot) 255⟧ := by
  unfold execCall call read_from_storage_split_offset_bool
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, nil]
  simp only [LetPrimCall', AssignPrimCall', evalArgs, evalTail, cons', head',
             reverse', multifill', PrimCall', Lit', Var', execPrimCall,
             evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMSload', EVMAnd']
  -- reduce every `multifill [x] [v]` to an `insert`; revive is identity.
  simp only [multifill_cons, multifill_nil]
  rw [reviveJump_insert (by rw [isOk_insert]; apply isOk_initcall_of_isOk; trivial)]
  -- the parameter `slot` is read off the initcall binding.
  rw [lookup_initcall_1]
  -- the body evm equals the caller evm (initcall only resets the varstore).
  have hevm : (initcall ["slot"] [slot] (Ok evm store)).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  rw [hevm]
  -- `split_expr_0` is bound to `evm.sload slot` (both occurrences).
  rw [lookup_insert' (by rw [isOk_insert]; apply isOk_initcall_of_isOk; trivial)]
  rw [lookup_insert' (by apply isOk_initcall_of_isOk; trivial)]
  -- restore the caller store and keep the body evm = evm.
  simp only [overwrite?_of_Ok]
  rw [setStore_insert, setStore_insert, setStore_initcall, setStore_same]

/--
  Closed form for `cleanup_bool(value)`: the body is
  `let s0 := iszero(value); cleaned := iszero(s0)`, pure, so the evm is unchanged
  and the return variable `v` is bound to `fromBool (fromBool (value = 0) = 0)`
  (i.e. the boolean normalisation of `value`).
-/
lemma cleanup_call_state
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {value : Literal} {v : Identifier} :
    execCall (fuel+1) cleanup_bool [v] (Ok evm store, [value])
      = (Ok evm store)⟦v ↦ fromBool (fromBool (value = 0) = 0)⟧ := by
  unfold execCall call cleanup_bool
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, nil]
  simp only [LetPrimCall', AssignPrimCall', evalArgs, evalTail, cons', head',
             reverse', multifill', PrimCall', Lit', Var', execPrimCall,
             evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero']
  simp only [multifill_cons, multifill_nil]
  rw [reviveJump_insert (by rw [isOk_insert]; apply isOk_initcall_of_isOk; trivial)]
  rw [lookup_initcall_1]
  rw [lookup_insert' (by rw [isOk_insert]; apply isOk_initcall_of_isOk; trivial)]
  rw [lookup_insert' (by apply isOk_initcall_of_isOk; trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_insert, setStore_insert, setStore_initcall, setStore_same]

/-- Specialisation: `cleanup_bool(0)` returns `0`. -/
lemma cleanup_call_zero
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {v : Identifier} :
    execCall (fuel+1) cleanup_bool [v] (Ok evm store, [0])
      = (Ok evm store)⟦v ↦ 0⟧ := by
  rw [cleanup_call_state]
  simp only [fromBool, Bool.toUInt256, decide_True, cond_true]
  rfl

/-- The keccak256 EVM op preserves the `reverted` flag on either branch (it only
    writes the keccak map, or records a hash collision). -/
lemma keccak256_reverted (e : EVMState) (a b : UInt256) :
    (match e.keccak256 a b with
      | .some r => r.snd
      | .none   => e.addHashCollision).reverted = e.reverted := by
  unfold EVMState.keccak256
  simp only
  cases Finmap.lookup (EVMState.mkInterval e.machine_state a b) e.keccak_map with
  | some val => simp only
  | none =>
    rcases hp : e.keccak_range.partition (fun x => x ∈ e.used_range) with ⟨_, _ | _⟩ <;>
      simp only [hp] <;> rfl

/-- The `keccak256` PRIMOP, applied to an `Ok` state, preserves the `reverted`
    flag of the underlying evm.  (Either branch only writes the keccak map or
    records a hash collision.)  This isolates the keccak `match` so the block
    replay never has to unfold it. -/
lemma keccak_primCall_reverted {s : State} {a b : Literal} (h : isOk s) :
    (primCall s .Keccak256 [a, b]).1.evm.reverted = s.evm.reverted := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h
  rw [EVMKeccak256']
  cases hk : (Ok evm₀ store).evm.keccak256 a b with
  | none => simp only [hk]; rfl
  | some r =>
    simp only [hk]
    have hh := keccak256_reverted (Ok evm₀ store).evm a b
    rw [hk] at hh
    rw [show ((Ok evm₀ store).setEvm r.snd).evm = r.snd from rfl, hh]

/--
  The trailing `mapping_index_access(...)` call (the block's last statement,
  `mstore; mstore; keccak256`) PRESERVES the `reverted` flag: it only writes
  memory and the keccak map.  Hence once the replay-CHECK has reverted, this
  recomputation cannot clear the revert.
-/
lemma mapping_index_preserves_reverted
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {key : Literal} {v : Identifier} :
    (execCall (fuel+1) mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17749
        [v] (Ok evm store, [key])).evm.reverted = evm.reverted := by
  unfold execCall call mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17749
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, nil]
  simp only [ExprStmtPrimCall', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMstore']
  -- Keep the keccak as a `primCall`; reduce the empty-var mstore multifills.
  simp only [multifill', multifill_nil, multifill_cons, overwrite?_of_Ok]
  -- The body state is `(primCall <mstore-mstore state> Keccak256 [0,64]).1` with the
  -- `dataSlot` return inserted; the keccak primop preserves reverted (both branches).
  -- `host` = the mstore/mstore-updated state (two `setEvm`s).
  set host := (((Ok evm store)☎️⟦["key"], [key]⟧)
      🇪⟦((Ok evm store)☎️⟦["key"], [key]⟧).evm.mstore 0
          (((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!!)⟧)
      🇪⟦(((Ok evm store)☎️⟦["key"], [key]⟧)
          🇪⟦((Ok evm store)☎️⟦["key"], [key]⟧).evm.mstore 0
              (((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!!)⟧).evm.mstore 32 208⟧
      with hhost
  have hhost_ok : isOk host := by
    rw [hhost, isOk_setEvm, isOk_setEvm]; apply isOk_initcall_of_isOk; trivial
  have hhost_revert : host.evm.reverted = evm.reverted := by
    rw [hhost]
    simp only [evm_setEvm_of_isOk (show isOk ((Ok evm store)☎️⟦["key"], [key]⟧)
                from isOk_initcall_of_isOk trivial), mstore_reverted]
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  -- the keccak primop preserves reverted (both branches), so the body state's evm
  -- has reverted = host.evm.reverted = evm.reverted.
  have hbody : (primCall host .Keccak256 [(0 : Literal), 64]).1.evm.reverted
      = evm.reverted := by
    rw [keccak_primCall_reverted hhost_ok, hhost_revert]
  have hbody_ok : isOk (primCall host .Keccak256 [(0 : Literal), 64]).1 := by
    rw [EVMKeccak256']
    cases host.evm.keccak256 0 64 <;> simp only [isOk_setEvm] <;> exact hhost_ok
  -- peel the call wrappers around the keccak-primop result state.  The `dataSlot`
  -- multifill keeps the evm; reviveJump on an Ok state is the identity; overwrite?
  -- of the Ok caller keeps the body; setStore keeps the evm.
  -- the keccak-primop result state is Ok; expose it so the wrappers reduce.
  obtain ⟨ek, sk, hok⟩ := State_of_isOk hbody_ok
  rw [hok] at hbody ⊢
  have hek : ek.reverted = evm.reverted := by rw [← hbody]; rfl
  -- multifill over Ok = Ok (evm preserved), reviveJump id, setStore keeps evm = ek.
  have hmf : isOk (multifill ["dataSlot"] (primCall host .Keccak256 [(0:Literal), 64]).2 (Ok ek sk)) :=
    isOk_multifill (by trivial)
  rw [evm_insert, evm_setStore, evm_reviveJump_of_isOk hmf, evm_multifill]
  exact hek

/-- ============================================================================
    MAIN THEOREM — CROSS-TRANSACTION WITHDRAWAL REPLAY PROTECTION.

    Running the replay-CHECK block `block_4604436955705083701` of
    `finalizeWithdrawal` from an `Ok evm store` state whose stored
    `isWithdrawalFinalized` flag for the withdrawal is ALREADY SET — formalised
    as the read value being nonzero, `Fin.land (evm.sload slot) 255 ≠ 0`, where
    `slot` is the nullifier slot bound to `split_expr_7` — ends with the run
    `reverted`.  This is the genuine anti-double-spend guarantee: a withdrawal
    that was already finalised cannot be finalised again.

    Precondition form: `store["split_expr_7"]!! = slot` (the precomputed nullifier
    slot entering the CHECK block) and `Fin.land (evm.sload slot) 255 ≠ 0` (its
    persistent finalised byte is set).
    ============================================================================ -/
theorem replay_protection_check_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {s₉ : State} {slot key : Literal}
    (hslot : (Ok evm store)["split_expr_7"]!! = slot)
    (hkey  : (Ok evm store)["_1"]!! = key)
    (hset  : Fin.land (evm.sload slot) 255 ≠ 0)
    (hexec : exec (fuel+1) block_4604436955705083701 (Ok evm store) = s₉) :
    s₉.evm.reverted = true := by
  rw [← hexec]
  unfold block_4604436955705083701
  -- statement 1: split_expr_8 := read(split_expr_7)  -- reads the finalised byte.
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append]
  rw [show (Ok evm store)["split_expr_7"]!! = slot from hslot, read_call_state]
  -- statement 2: split_expr_9 := iszero(split_expr_8)   (= 0, since the byte ≠ 0)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append]
  rw [EVMIszero']
  simp only [head', List.head!]
  rw [lookup_insert' (by trivial)]
  -- `iszero (Fin.land … ≠ 0) = 0`
  rw [show fromBool (Fin.land (evm.sload slot) 255 = 0) = (0 : UInt256) by
        rw [decide_eq_false hset]; rfl]
  -- statement 3: split_expr_10 := cleanup(split_expr_9 = 0)  (= 0)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             multifill_cons, multifill_nil]
  rw [lookup_insert' (by rw [isOk_insert]; trivial)]
  simp only [insert_Ok]
  rw [cleanup_call_zero]
  -- statement 4: require_helper(split_expr_10 = 0)  -- REVERTS.
  rw [cons, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             multifill_cons, multifill_nil]
  rw [lookup_insert' (by trivial)]
  simp only [insert_Ok]
  -- now the require_helper runs with argument 0 over an Ok state; record the result
  -- state `s_req`: it is Ok (the revert leaves an Ok-shaped state) and reverted.
  generalize hreq : execCall (fuel+1) require_helper_error_WithdrawalAlreadyFinalized []
      (Ok evm (Finmap.insert "split_expr_10" 0
        (Finmap.insert "split_expr_9" 0
          (Finmap.insert "split_expr_8" (Fin.land (evm.sload slot) 255) store))), [0]) = s_req
  have hreq_revert : s_req.evm.reverted = true :=
    require_helper_reverts_of_zero hreq
  have hreq_ok : isOk s_req := by
    rw [← hreq]; exact require_call_isOk
  -- statement 5: split_expr_11 := mapping_index(_1); preserves the revert.
  obtain ⟨e_req, st_req, hreq_eq⟩ := State_of_isOk hreq_ok
  rw [cons, LetCall', nil]
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append]
  rw [hreq_eq] at hreq_revert ⊢
  rw [mapping_index_preserves_reverted]
  exact hreq_revert

-- `#print axioms replay_protection_check_reverts` reports
-- `[propext, Quot.sound, Classical.choice]` — NO `sorryAx`.  Because the replay
-- CHECK reverts BEFORE the SET block (which calls `fun_verifyWithdrawal`, the only
-- transitive source of the generated `mcopy`/`tstore` sorry stubs), this theorem is
-- entirely free of the A3 sorryAx that taints `modifier_nonReentrant_892_user.lean`.

/-! ============================================================================
    SET-SIDE COMPANION — the SET write helper actually SETS the flag.

    The replay CHECK above (`replay_protection_check_reverts`) shows that an
    already-finalised withdrawal CANNOT be re-finalised.  The companion property,
    proved here, is that the SET write helper
    `update_storage_value_offset_bool_to_bool_17751(slot)` genuinely SETS the
    finalised byte at `slot` to `1`.  Together they justify the check-then-set
    discipline of `finalizeWithdrawal`.

    The write helper body is
        split_expr_0 := sload(slot)
        split_expr_1 := not(255)
        split_expr_2 := and(split_expr_0, split_expr_1)
        split_expr_3 := or(split_expr_2, 1)
        sstore(slot, split_expr_3)
    i.e. it clears the low byte then ORs in `1`, writing `(x &&& ~255) ||| 1`.

    These lemmas touch ONLY sload/and/or/not/sstore — NO `fun_verifyWithdrawal` —
    so they are entirely A3-free (axioms `[propext, Quot.sound, Classical.choice]`,
    no `sorryAx`), exactly like the CHECK-side theorem above.

    NOTE: proving that the slot CHECKED (`split_expr_7`) equals the slot SET
    (`split_expr_13`) requires keccak determinism/consistency across the two
    `mapping_index_access` recomputations — now DISCHARGED at statement level by
    `check_set_slots_eq` at the bottom of this file (frame-conditioned, via
    `specs/KeccakDeterminism.lean`; axiom-free).
    ============================================================================ -/

private lemma ne_01 : ("split_expr_0" : Identifier) ≠ "split_expr_1" := by decide
private lemma ne_s0 : ("slot" : Identifier) ≠ "split_expr_0" := by decide
private lemma ne_s1 : ("slot" : Identifier) ≠ "split_expr_1" := by decide
private lemma ne_s2 : ("slot" : Identifier) ≠ "split_expr_2" := by decide
private lemma ne_s3 : ("slot" : Identifier) ≠ "split_expr_3" := by decide

/--
  Closed form for the SET write `update_storage_value_offset_bool_to_bool_17751(slot)`
  (analogue of `read_call_state`).  The body reads `slot`, clears its low byte
  (`and(_, not 255)`) and ORs in `1`, then stores it back; since `rets = []`, the
  call returns the caller state with the evm updated by a single `sstore` of the new
  value `(evm.sload slot &&& ~255) ||| 1` and the varstore restored.
-/
lemma update_storage_writes_flag
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slot : Literal} :
    execCall (fuel+1) update_storage_value_offset_bool_to_bool_17751 []
        (Ok evm store, [slot])
      = (Ok evm store).setEvm
          (evm.sstore slot (Fin.lor (Fin.land (evm.sload slot) (Clear.UInt256.lnot 255)) 1)) := by
  unfold execCall call update_storage_value_offset_bool_to_bool_17751
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, cons, cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall', evalArgs, evalTail, cons', head',
             reverse', multifill', PrimCall', Lit', Var', execPrimCall,
             evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMSload', EVMNot', EVMAnd', EVMOr', EVMSstore']
  simp only [multifill_cons, multifill_nil]
  -- abbreviations for the four computed values; generalize them to keep terms small.
  generalize hsv : evm.sload slot = sv
  set m255 := Clear.UInt256.lnot 255 with hm255
  set v2 := Fin.land sv m255 with hv2
  set v3 := Fin.lor v2 1 with hv3
  -- body evm = caller evm (initcall only resets the varstore)
  have hevm : (initcall ["slot"] [slot] (Ok evm store)).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hslot : (Ok evm store)☎️⟦["slot"], [slot]⟧["slot"]!! = slot := lookup_initcall_1
  have hok0 : isOk ((Ok evm store)☎️⟦["slot"], [slot]⟧) := isOk_initcall_of_isOk trivial
  have hok1 : isOk ((Ok evm store)☎️⟦["slot"], [slot]⟧⟦"split_expr_0" ↦ sv⟧) :=
    isOk_insert.mpr hok0
  have hok2 : isOk ((Ok evm store)☎️⟦["slot"], [slot]⟧⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧) :=
    isOk_insert.mpr hok1
  have hok3 : isOk ((Ok evm store)☎️⟦["slot"], [slot]⟧⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧) :=
    isOk_insert.mpr hok2
  -- resolve the body evm and the `slot` parameter binding.
  rw [show (Ok evm store)☎️⟦["slot"], [slot]⟧.evm = evm from hevm, hslot, hsv]
  -- resolve the split_expr lookups (innermost-first).
  have l0 : ((Ok evm store)☎️⟦["slot"], [slot]⟧⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧)["split_expr_0"]!! = sv := by
    rw [lookup_insert_of_ne ne_01, lookup_insert' hok0]
  have l1 : ((Ok evm store)☎️⟦["slot"], [slot]⟧⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧)["split_expr_1"]!! = m255 :=
    lookup_insert' (var := "split_expr_1") (x := m255) hok1
  rw [l0, l1, ← hv2]
  have l2 : ((Ok evm store)☎️⟦["slot"], [slot]⟧⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧)["split_expr_2"]!! = v2 :=
    lookup_insert' (var := "split_expr_2") (x := v2) hok2
  rw [l2, ← hv3]
  have lslot : ((Ok evm store)☎️⟦["slot"], [slot]⟧⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧)["slot"]!! = slot := by
    rw [lookup_insert_of_ne ne_s3, lookup_insert_of_ne ne_s2,
        lookup_insert_of_ne ne_s1, lookup_insert_of_ne ne_s0]; exact hslot
  have l3 : ((Ok evm store)☎️⟦["slot"], [slot]⟧⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧)["split_expr_3"]!! = v3 :=
    lookup_insert' hok3
  rw [lslot, l3]
  -- the sstore reads `.evm` of the chain, which equals the caller evm.
  rw [show ((Ok evm store)☎️⟦["slot"], [slot]⟧⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧).evm = evm from by
        simp only [evm_insert]; exact hevm]
  -- inner state is Ok; reviveJump identity, overwrite? of Ok caller keeps it.
  have hinner_ok : isOk (((Ok evm store)☎️⟦["slot"], [slot]⟧⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧)🇪⟦evm.sstore slot v3⟧) := by
    rw [isOk_setEvm]; exact isOk_insert.mpr hok3
  rw [reviveJump_of_isOk hinner_ok, overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hinner_ok
  have hi_evm : ei = evm.sstore slot v3 := by
    have h := congrArg State.evm hi
    rw [evm_setEvm_of_isOk (isOk_insert.mpr hok3)] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]; rfl

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

/-- **Pure low-byte lemma.** The value written by the SET helper,
`(x &&& ~255) ||| 1`, has low byte `and(_,255) = 1`.  Proved by `Nat.testBit`
reasoning (a 256-bit `decide` is infeasible). -/
theorem fin_mask_one (x : UInt256) :
    Fin.land (Fin.lor (Fin.land x (Clear.UInt256.lnot 255)) 1) 255 = 1 := by
  apply Fin.ext
  have hlnot : (Clear.UInt256.lnot 255 : UInt256).val = UInt256.size - 256 := by
    unfold Clear.UInt256.lnot; rfl
  rcases x with ⟨a, ha⟩
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

/-- The SET value is nonzero (its low byte is `1`). -/
theorem fin_mask_ne_zero (x : UInt256) :
    Fin.lor (Fin.land x (Clear.UInt256.lnot 255)) 1 ≠ 0 := by
  intro h
  have := fin_mask_one x
  rw [h] at this
  simp only [Fin.land] at this
  exact absurd this (by decide)

/-- Re-reading the slot just written returns the stored value, provided the
contract's own account exists (the realistic deployed-contract case) and the value
is nonzero.  (The storage model returns `0` for a missing account, hence the
hypothesis.) -/
theorem sload_sstore_self_of_nonzero (σ : EVMState) (b val : UInt256)
    (hv : val ≠ 0)
    (hacc : (σ.lookupAccount σ.execution_env.code_owner).isSome) :
    (σ.sstore b val).sload b = val := by
  unfold EVMState.sstore EVMState.sload
  cases h : σ.lookupAccount σ.execution_env.code_owner with
  | none => rw [h] at hacc; simp at hacc
  | some act =>
    simp only [h]
    unfold EVMState.lookupAccount EVMState.updateAccount
    simp only [Finmap.lookup_insert]
    unfold Account.updateStorage Account.lookupStorage
    rw [if_neg (by simpa using hv), Finmap.lookup_insert]

/-- **KEY COROLLARY (the SET sets the flag).** After running the SET write helper
from `Ok evm store`, the post-state `s'` has its `isWithdrawalFinalized` byte SET:
`Fin.land (s'.evm.sload slot) 255 = 1` (hence `≠ 0`).  Requires the contract's own
account to exist (always true for a deployed contract), which is needed because the
storage model returns `0` for a missing account.  This is the SET-side companion to
`replay_protection_check_reverts`. -/
theorem update_storage_sets_low_byte
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slot : Literal} {s' : State}
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome)
    (hexec : execCall (fuel+1) update_storage_value_offset_bool_to_bool_17751 []
                (Ok evm store, [slot]) = s') :
    Fin.land (s'.evm.sload slot) 255 = 1 := by
  rw [← hexec, update_storage_writes_flag]
  rw [evm_setEvm_of_isOk (by trivial : isOk (Ok evm store))]
  rw [sload_sstore_self_of_nonzero evm slot _ (fin_mask_ne_zero (evm.sload slot)) hacc]
  exact fin_mask_one (evm.sload slot)

/-! ============================================================================
    COMPOSITION — SET-THEN-REPLAY-REVERTS (end-to-end anti-double-spend).

    This chains the two A3-free lemmas above into a single state-to-state
    statement:

      1. `update_storage_sets_low_byte` — running the SET write helper
         `update_storage_value_offset_bool_to_bool_17751` at `slot` from
         `Ok evm store` yields a post-write state `s_set` whose finalised byte at
         `slot` is `1` (i.e. `Fin.land (s_set.evm.sload slot) 255 = 1`).  Carries
         the benign hypothesis `hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome`
         (a deployed contract's own account exists; the storage model returns `0`
         otherwise).

      2. `replay_protection_check_reverts` — running the replay-CHECK block
         `block_4604436955705083701` from a state whose finalised byte at the slot
         bound to `split_expr_7` is nonzero ends with `evm.reverted = true`.

    The link is exact: the byte that lemma 1 proves is `1` at `slot` is precisely
    the `hset : Fin.land evm₁.sload slot 255 ≠ 0` that lemma 2 demands (`1 ≠ 0`).
    So: run the SET helper to obtain `s_set = Ok evm₁ store`; rebind the CHECK
    input store so `split_expr_7 ↦ slot`; the low-byte fact discharges `hset`; and
    `replay_protection_check_reverts` discharges the rest.  No new hypotheses about
    the CHECK's storage are introduced — `evm₁.sload slot` is exactly the byte
    lemma 1 set.

    CAVEAT (by construction): this theorem uses `slot` as the SHARED variable
    threaded through both the SET (lemma 1's `slot`) and the CHECK
    (`split_expr_7 ↦ slot`).  It does NOT itself prove that the slot the contract
    SETS (`split_expr_13`) equals the slot it later CHECKS (`split_expr_7`); that
    `split_expr_7 == split_expr_13` slot-equality is a keccak-determinism fact —
    now proven separately, at statement level, by `check_set_slots_eq` at the
    bottom of this file (both slots are the same triple accessor chain over
    `(_1,_2,_3)`; the re-run provably replays the cached keccak slots).  Together
    they give the genuine "a finalised withdrawal cannot be re-finalised"
    composition.

    Like its two components this touches NO `fun_verifyWithdrawal`, so it is A3-free:
    `#print axioms replay_after_set_reverts` reports `[propext, Quot.sound, Classical.choice]`.
    ============================================================================ -/
theorem replay_after_set_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    {slot : Literal} {s_set s₉ : State}
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome)
    -- SET: run the write helper at `slot`; `s_set` is the post-write state.
    (hset_exec : execCall (fuel+1) update_storage_value_offset_bool_to_bool_17751 []
                    (Ok evm store, [slot]) = s_set)
    -- the CHECK runs from `s_set`'s evm with `split_expr_7 ↦ slot` (and `_1`
    -- carrying its own lookup as the `key`); `s₉` is the post-CHECK state.
    (hcheck_exec : exec (fuel+1) block_4604436955705083701
                      ((Ok s_set.evm store)⟦"split_expr_7" ↦ slot⟧) = s₉) :
    s₉.evm.reverted = true := by
  -- The SET genuinely sets the finalised byte at `slot` to `1` (lemma 1).
  have hbyte : Fin.land (s_set.evm.sload slot) 255 = 1 :=
    update_storage_sets_low_byte hacc hset_exec
  -- `1 ≠ 0` is exactly the `hset` lemma 2 needs.
  have hbyte_ne : Fin.land (s_set.evm.sload slot) 255 ≠ 0 := by
    rw [hbyte]; decide
  -- Expose the CHECK input as an `Ok`-shaped state so lemma 2 (stated over
  -- `Ok evm store`) applies and the `split_expr_7 ↦ slot` binding is visible.
  rw [insert_Ok] at hcheck_exec
  -- The CHECK input store binds `split_expr_7` to `slot` by construction.
  have hslot : (Ok s_set.evm (store.insert "split_expr_7" slot))["split_expr_7"]!! = slot := by
    rw [← insert_Ok]; exact lookup_insert' (var := "split_expr_7") (x := slot) (by trivial)
  -- `_1` is whatever it looks up to; lemma 2's `key` is universally quantified.
  apply replay_protection_check_reverts
    (slot := slot)
    (key := (Ok s_set.evm (store.insert "split_expr_7" slot))["_1"]!!)
    hslot rfl hbyte_ne hcheck_exec

/-! ============================================================================
    SLOT-EQUALITY — the slot CHECKED equals the slot SET (keccak determinism).

    This closes the linkage flagged as OUT OF SCOPE above: that the nullifier
    slot the modifier CHECKS (`split_expr_7`) equals the slot it later SETS
    (`split_expr_13`).  Both are the SAME triple-nested keccak accessor chain
    over the same arguments `(_1, _2, _3)` and base slot `208`:

        split_expr_5  := mapping_index_access_…_17749(_1)              -- base 208
        split_expr_6  := mapping_index_access_…(split_expr_5, _2)
        split_expr_7  := mapping_index_access_…(split_expr_6, _3)      -- CHECK slot
        …  (read / iszero / cleanup_bool / require — no memory writes,
            no keccak-cache drops on the success path)  …
        split_expr_11 := mapping_index_access_…_17749(_1)
        split_expr_12 := mapping_index_access_…(split_expr_11, _2)
        split_expr_13 := mapping_index_access_…(split_expr_12, _3)     -- SET slot

    In Clear's freshness model, keccak memoizes every hashed 64-byte interval in
    `keccak_map`, so the re-run HITS the cache at every level and returns the
    same three slots — PROVIDED the two runs' preimages coincide.  Each accessor
    writes `key` at word 0 and `base` at word 32 and hashes `[0, 64)`; but the
    model's `lookupMemory` makes the interval also depend on the junk window
    `[64, 95)`.  Hence the two honest frame hypotheses of the theorem: between
    the CHECK chain's end and the SET chain's start (i) memory bytes `[64, 95)`
    are unchanged and (ii) no keccak-cache entry is dropped — both TRUE of the
    actual intervening statements (sload/iszero/cleanup/require-success touch
    neither).  The one model-caveat hypothesis is `hclean` (no hash-collision
    fallback fired on the CHECK side), matching the A6 caveat style of the other
    keccak theorems.

    The determinism core is `Clear.KeccakDeterminism.accessor_chain_deterministic`
    (axiom-free); here we supply the CLOSED FORMS of the two generated accessor
    helpers and instantiate.  `#print axioms check_set_slots_eq` reports
    `[propext, Quot.sound, Classical.choice]` — no `sorryAx`, no keccak axioms.
    ============================================================================ -/

open Clear.KeccakDeterminism

/-- The keccak PRIMOP in `keccakOut` form (fuses both branches of
`EVMKeccak256'` into the total function `keccakOut`). -/
lemma primCall_keccakOut {s : State} {a b : Literal} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (keccakOut s.evm a b).2, [(keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

/-- Variable lookup is unaffected by `setEvm` (on an `Ok` state). -/
private lemma lookup_setEvm_of_isOk {s : State} {e : EVMState} {k : Identifier}
    (h : isOk s) : (s.setEvm e)[k]!! = s[k]!! := by
  obtain ⟨evm₀, st, rfl⟩ := State_of_isOk h; rfl

/--
  Closed form for `mapping_index_access_…_17749(key)` (the base-208 level-1
  accessor: `mstore(0, key); mstore(32, 208); dataSlot := keccak256(0, 64)`):
  the call returns the caller state with the evm advanced by one `accOut` step
  at `(key, 208)` and the return variable bound to the produced slot.
-/
lemma mapping_index_17749_call_acc
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {key : Literal} {v : Identifier} :
    execCall (fuel+1) mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17749
        [v] (Ok evm store, [key])
      = Ok (accOut evm key 208).2 (store.insert v (accOut evm key 208).1) := by
  unfold execCall call mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17749
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, nil]
  simp only [ExprStmtPrimCall', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMstore']
  simp only [multifill', multifill_nil, multifill_cons, overwrite?_of_Ok]
  rw [primCall_keccakOut]
  -- name the double-mstore host state (same shape as `mapping_index_preserves_reverted`)
  have hok₀ : isOk ((Ok evm store)☎️⟦["key"], [key]⟧) := isOk_initcall_of_isOk trivial
  have hevm₀ : ((Ok evm store)☎️⟦["key"], [key]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hkey : ((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!! = key := lookup_initcall_1
  set host := (((Ok evm store)☎️⟦["key"], [key]⟧)
      🇪⟦((Ok evm store)☎️⟦["key"], [key]⟧).evm.mstore 0
          (((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!!)⟧)
      🇪⟦(((Ok evm store)☎️⟦["key"], [key]⟧)
          🇪⟦((Ok evm store)☎️⟦["key"], [key]⟧).evm.mstore 0
              (((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!!)⟧).evm.mstore 32 208⟧
      with hhost
  have hhost_ok : isOk host := by
    rw [hhost, isOk_setEvm, isOk_setEvm]; exact hok₀
  have hhost_evm : host.evm = (evm.mstore 0 key).mstore 32 208 := by
    rw [hhost, evm_setEvm_of_isOk (by rw [isOk_setEvm]; exact hok₀),
        evm_setEvm_of_isOk hok₀, hevm₀, hkey]
  rw [hhost_evm]
  -- the RHS `accOut` is definitionally this keccakOut step
  unfold accOut
  generalize hout : keccakOut ((evm.mstore 0 key).mstore 32 208) 0 64 = out
  -- reduce the body's `multifill` to an insert, resolve the `dataSlot` return
  -- lookup, then peel the call wrappers
  simp only [multifill_cons, multifill_nil]
  have hsetEvm_ok : isOk (host.setEvm out.2) := by
    rw [isOk_setEvm]; exact hhost_ok
  have hin_ok : isOk ((host.setEvm out.2)⟦"dataSlot" ↦ out.1⟧) := by
    rw [isOk_insert]; exact hsetEvm_ok
  rw [lookup_insert' hsetEvm_ok]
  rw [reviveJump_of_isOk hin_ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = out.2 := by
    have h := congrArg State.evm hi
    rw [evm_insert, evm_setEvm_of_isOk hhost_ok] at h
    exact h.symm
  rw [hi, setStore_ok]
  simp only [insert_Ok]
  rw [hi_evm]

/--
  Closed form for the level-2/3 accessor
  `mapping_index_access_…(slot, key)` (`mstore(0, key); mstore(32, slot);
  dataSlot := keccak256(0, 64)`): one `accOut` step at `(key, slot)`.
-/
lemma mapping_index_call_acc
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slotArg key : Literal} {v : Identifier} :
    execCall (fuel+1) mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256
        [v] (Ok evm store, [slotArg, key])
      = Ok (accOut evm key slotArg).2 (store.insert v (accOut evm key slotArg).1) := by
  unfold execCall call mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, nil]
  simp only [ExprStmtPrimCall', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMstore']
  simp only [multifill', multifill_nil, multifill_cons, overwrite?_of_Ok]
  rw [primCall_keccakOut]
  have hok₀ : isOk ((Ok evm store)☎️⟦["slot", "key"], [slotArg, key]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm₀ : ((Ok evm store)☎️⟦["slot", "key"], [slotArg, key]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hkey : ((Ok evm store)☎️⟦["slot", "key"], [slotArg, key]⟧)["key"]!! = key :=
    lookup_initcall_2 (by decide)
  have hslot : ((Ok evm store)☎️⟦["slot", "key"], [slotArg, key]⟧)["slot"]!! = slotArg :=
    lookup_initcall_1
  set s₀ := (Ok evm store)☎️⟦["slot", "key"], [slotArg, key]⟧ with hs₀
  set s₁ := s₀🇪⟦s₀.evm.mstore 0 (s₀["key"]!!)⟧ with hs₁
  have hs₁_ok : isOk s₁ := by rw [hs₁, isOk_setEvm]; exact hok₀
  set host := s₁🇪⟦s₁.evm.mstore 32 (s₁["slot"]!!)⟧ with hhost
  have hhost_ok : isOk host := by rw [hhost, isOk_setEvm]; exact hs₁_ok
  have hhost_evm : host.evm = (evm.mstore 0 key).mstore 32 slotArg := by
    rw [hhost, evm_setEvm_of_isOk hs₁_ok, hs₁, evm_setEvm_of_isOk hok₀, hevm₀, hkey,
        lookup_setEvm_of_isOk hok₀, hslot]
  rw [hhost_evm]
  unfold accOut
  generalize hout : keccakOut ((evm.mstore 0 key).mstore 32 slotArg) 0 64 = out
  simp only [multifill_cons, multifill_nil]
  have hsetEvm_ok : isOk (host.setEvm out.2) := by
    rw [isOk_setEvm]; exact hhost_ok
  have hin_ok : isOk ((host.setEvm out.2)⟦"dataSlot" ↦ out.1⟧) := by
    rw [isOk_insert]; exact hsetEvm_ok
  rw [lookup_insert' hsetEvm_ok]
  rw [reviveJump_of_isOk hin_ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = out.2 := by
    have h := congrArg State.evm hi
    rw [evm_insert, evm_setEvm_of_isOk hhost_ok] at h
    exact h.symm
  rw [hi, setStore_ok]
  simp only [insert_Ok]
  rw [hi_evm]

/-- **THE SLOT-EQUALITY THEOREM** — `split_expr_13 = split_expr_7`.

Running the triple accessor chain twice with the same keys `(k₁, k₂, k₃)` — the
CHECK chain producing `v₅/v₆/v₇` from `Ok evm₀ st₀` and the SET chain producing
`v₁₁/v₁₂/v₁₃` from `Ok evmM stM` — returns the SAME final slot, provided the
intervening execution (i) left memory bytes `[64, 95)` unchanged (`hmem`),
(ii) dropped no keccak-cache entry (`hmono`), and (iii) the CHECK chain ended
hash-collision-free (`hclean`).  Hypotheses (i)–(ii) hold of the actual
statements between the chains (sload/iszero/cleanup/require-success touch
neither memory nor the keccak cache); (iii) is the standard A6 model caveat. -/
theorem check_set_slots_eq
    {evm₀ evmM : EVMState} {st₀ stM : VarStore}
    {f₅ f₆ f₇ f₁₁ f₁₂ f₁₃ : ℕ} {k₁ k₂ k₃ b₆ b₇ b₁₂ b₁₃ : Literal}
    {s₅ s₆ s₇ s₁₁ s₁₂ s₁₃ : State}
    {v₅ v₆ v₇ v₁₁ v₁₂ v₁₃ : Identifier}
    -- CHECK-side chain (split_expr_5/6/7)
    (h₅ : execCall (f₅+1)
        mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17749
        [v₅] (Ok evm₀ st₀, [k₁]) = s₅)
    (h₆ : execCall (f₆+1)
        mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256
        [v₆] (s₅, [b₆, k₂]) = s₆)
    (hb₆ : b₆ = s₅[v₅]!!)
    (h₇ : execCall (f₇+1)
        mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256
        [v₇] (s₆, [b₇, k₃]) = s₇)
    (hb₇ : b₇ = s₆[v₆]!!)
    -- frame: the intervening execution (CHECK-chain end → SET-chain start)
    (hmem : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i evmM.machine_state.memory
        = Finmap.lookup i s₇.evm.machine_state.memory)
    (hmono : ∀ (I : List UInt256) (w : UInt256),
      Finmap.lookup I s₇.evm.keccak_map = some w
        → Finmap.lookup I evmM.keccak_map = some w)
    -- SET-side chain (split_expr_11/12/13)
    (h₁₁ : execCall (f₁₁+1)
        mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17749
        [v₁₁] (Ok evmM stM, [k₁]) = s₁₁)
    (h₁₂ : execCall (f₁₂+1)
        mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256
        [v₁₂] (s₁₁, [b₁₂, k₂]) = s₁₂)
    (hb₁₂ : b₁₂ = s₁₁[v₁₁]!!)
    (h₁₃ : execCall (f₁₃+1)
        mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256
        [v₁₃] (s₁₂, [b₁₃, k₃]) = s₁₃)
    (hb₁₃ : b₁₃ = s₁₂[v₁₂]!!)
    -- no keccak-collision fallback on the CHECK side (A6 model caveat)
    (hclean : s₇.evm.hash_collision = false) :
    s₁₃[v₁₃]!! = s₇[v₇]!! := by
  -- Rewrite all six calls into their `accOut` closed forms.
  rw [mapping_index_17749_call_acc] at h₅
  -- s₅ is now explicit; resolve its return-variable lookup.
  have hs₅v : s₅[v₅]!! = (accOut evm₀ k₁ 208).1 := by
    rw [← h₅, ← insert_Ok]; exact lookup_insert' (by trivial)
  rw [hb₆, hs₅v] at h₆
  rw [← h₅] at h₆
  rw [mapping_index_call_acc] at h₆
  have hs₆v : s₆[v₆]!! = (accOut (accOut evm₀ k₁ 208).2 k₂ (accOut evm₀ k₁ 208).1).1 := by
    rw [← h₆, ← insert_Ok]; exact lookup_insert' (by trivial)
  rw [hb₇, hs₆v] at h₇
  rw [← h₆] at h₇
  rw [mapping_index_call_acc] at h₇
  have hs₇v : s₇[v₇]!!
      = (accOut (accOut (accOut evm₀ k₁ 208).2 k₂ (accOut evm₀ k₁ 208).1).2 k₃
          (accOut (accOut evm₀ k₁ 208).2 k₂ (accOut evm₀ k₁ 208).1).1).1 := by
    rw [← h₇, ← insert_Ok]; exact lookup_insert' (by trivial)
  have hs₇evm : s₇.evm
      = (accOut (accOut (accOut evm₀ k₁ 208).2 k₂ (accOut evm₀ k₁ 208).1).2 k₃
          (accOut (accOut evm₀ k₁ 208).2 k₂ (accOut evm₀ k₁ 208).1).1).2 := by
    rw [← h₇]; rfl
  -- Same for the SET-side chain.
  rw [mapping_index_17749_call_acc] at h₁₁
  have hs₁₁v : s₁₁[v₁₁]!! = (accOut evmM k₁ 208).1 := by
    rw [← h₁₁, ← insert_Ok]; exact lookup_insert' (by trivial)
  rw [hb₁₂, hs₁₁v] at h₁₂
  rw [← h₁₁] at h₁₂
  rw [mapping_index_call_acc] at h₁₂
  have hs₁₂v : s₁₂[v₁₂]!! = (accOut (accOut evmM k₁ 208).2 k₂ (accOut evmM k₁ 208).1).1 := by
    rw [← h₁₂, ← insert_Ok]; exact lookup_insert' (by trivial)
  rw [hb₁₃, hs₁₂v] at h₁₃
  rw [← h₁₂] at h₁₃
  rw [mapping_index_call_acc] at h₁₃
  have hs₁₃v : s₁₃[v₁₃]!!
      = (accOut (accOut (accOut evmM k₁ 208).2 k₂ (accOut evmM k₁ 208).1).2 k₃
          (accOut (accOut evmM k₁ 208).2 k₂ (accOut evmM k₁ 208).1).1).1 := by
    rw [← h₁₃, ← insert_Ok]; exact lookup_insert' (by trivial)
  -- Instantiate the determinism core.
  have hdet := accessor_chain_deterministic
    (σ₀ := evm₀) (σmid := evmM) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃) (b := 208)
    (h₅ := rfl) (h₆ := rfl) (h₇ := rfl)
    (hmem := by rw [hs₇evm] at hmem; exact hmem)
    (hmono := by rw [hs₇evm] at hmono; exact hmono)
    (h₁₁ := rfl) (h₁₂ := rfl) (h₁₃ := rfl)
    (hclean := by rw [hs₇evm] at hclean; exact hclean)
  rw [hs₁₃v, hs₇v]
  exact hdet.2.2

end

end generated.L1Nullifier.L1Nullifier
