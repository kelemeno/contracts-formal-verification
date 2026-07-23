import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5412558363375237105
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_880639588767859599

import generated.AtomicFlowManager.AtomicFlowManager.read_from_storage_split_offset_enum_LegState
import generated.AtomicFlowManager.AtomicFlowManager.validator_assert_enum_LegState
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_enum_LegState
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_bytes32_bytes32_enum_LegState
import generated.AtomicFlowManager.AtomicFlowManager.update_storage_value_offset_enum_LegState_to_enum_LegState_gen
import generated.AtomicFlowManager.AtomicFlowManager.update_storage_value_offset_enum_LegState_to_enum_LegState_7877_gen
import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7848
import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32

import specs.RevertModel
import specs.KeccakDeterminism

/-
  ATOMIC INTEROP — LEG STATE-MACHINE SAFETY for `AtomicFlowManager.claimRefund`.

  `claimRefund` is the money-moving end of the timeout path: it re-mints the
  burned source funds.  Its guard is the per-leg state machine
  (`Unset(0) → Committed(1) → Revertable(2) → Reverted(3)`), a TWO-step refund:
  `authorizeRefund` marks `Committed → Revertable(2)` per missing-leg absence
  proof (the base `update_storage_…_enum_LegState` helper, `or(…, 2)`); then
  `claimRefund` requires the state to be EXACTLY `Revertable(2)` (else
  `ManagerLegNotRevertable`) and marks `Reverted(3)`
  (`update_storage_…_enum_LegState_7877`, `or(…, 3)`) before paying:

      _5            := read_from_storage_split_offset_enum_LegState(split_expr_21)
      validator_assert_enum_LegState(_5)
      split_expr_22 := eq(_5, 2)                        -- CHECK: state == Revertable
      if iszero(split_expr_22) { … revert(0, len) }     -- otherwise REVERT
      …
      update_storage_…_enum_LegState_7877(split_expr_26) -- SET: state := Reverted(3)

  This file proves the CHECK and both SET (mark) halves as STATE PREDICATES
  (using the RevertModel `reverted` flag) and composes them:

  * `refund_check_reverts` — running the CHECK block + guard-if from any state
    whose stored leg byte is a valid LegState other than `Revertable(2)` ends
    `reverted = true`.  Instances: `Unset(0)` (a leg that never committed cannot
    be refunded), `Committed(1)` (no refund without `authorizeRefund`), and
    `Reverted(3)` (NO DOUBLE REFUND).
  * `refund_check_passes` — from `Revertable(2)` the CHECK falls through
    unchanged (up to the two scratch binds): `authorizeRefund`'s mark is
    exactly what unlocks the claim.
  * `update_storage_sets_revertable_byte` — the authorize-side mark (base
    helper) genuinely stores `Revertable(2)` into the slot's low byte.
  * `update_storage_sets_reverted_byte` — the claim-side mark (`_7877`)
    genuinely stores `Reverted(3)` into the slot's low byte.
  * `claim_after_authorize_passes` — end-to-end forward step: run the
    authorize mark at `slot`, then the CHECK on the post-write evm ⇒ the
    guard PASSES.
  * `reclaim_after_refund_reverts` — end-to-end: run the claim mark at `slot`,
    then re-run the CHECK on the post-write evm ⇒ the re-claim REVERTS
    (`3 ≠ 2`).  This is the "a leg is refunded at most once" anti-double-mint
    guarantee — the leg-level core of atomicity's no-double-spend direction.

  All theorems here are A3-free (no mcopy/tstore in the cone) — expect
  `#print axioms` = `[propext, Quot.sound, Classical.choice]`.

  (The slot CHECKED = slot SET linkage — `split_expr_21 == split_expr_26`, both
  the same 2-level keccak accessor chain over `(var__flowId, expr)` — is the
  2-level analog of the L1Nullifier `check_set_slots_eq` and is stated below as
  `claim_check_set_slots_eq`; the machinery lives in
  `specs/KeccakDeterminism.lean`.)
-/

namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager Clear.RevertModel

set_option maxRecDepth 6000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-- `insert` on an `Ok` state writes into the underlying varstore. -/
@[simp] lemma insert_Ok {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

/-- On an `Ok` state, `setEvm` overwrites the evm verbatim. -/
lemma evm_setEvm_of_isOk {s : State} {e : EVMState} (h : isOk s) :
    (s.setEvm e).evm = e := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

/-- `reviveJump` is the identity on `Ok` states. -/
lemma reviveJump_of_isOk {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

/-- Variable lookup is unaffected by `setEvm` (on an `Ok` state). -/
lemma lookup_setEvm_of_isOk {s : State} {e : EVMState} {k : Identifier}
    (h : isOk s) : (s.setEvm e)[k]!! = s[k]!! := by
  obtain ⟨evm₀, st, rfl⟩ := State_of_isOk h; rfl

/--
  Closed form for `read_from_storage_split_offset_enum_LegState(slot)`: the body
  is `let s0 := sload(slot); value := and(s0, 255)` — pure storage read; the call
  returns the caller state with `v ↦ Fin.land (evm.sload slot) 255`.
  (Byte-identical to the L1Nullifier bool read helper.)
-/
lemma read_legstate_call_state
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slot : Literal} {v : Identifier} :
    execCall (fuel+1) read_from_storage_split_offset_enum_LegState [v]
        (Ok evm store, [slot])
      = (Ok evm store)⟦v ↦ Fin.land (evm.sload slot) 255⟧ := by
  unfold execCall call read_from_storage_split_offset_enum_LegState
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, nil]
  simp only [LetPrimCall', AssignPrimCall', evalArgs, evalTail, cons', head',
             reverse', multifill', PrimCall', Lit', Var', execPrimCall,
             evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMSload', EVMAnd']
  simp only [multifill_cons, multifill_nil]
  rw [reviveJump_insert (by rw [isOk_insert]; apply isOk_initcall_of_isOk; trivial)]
  rw [lookup_initcall_1]
  have hevm : (initcall ["slot"] [slot] (Ok evm store)).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  rw [hevm]
  rw [lookup_insert' (by rw [isOk_insert]; apply isOk_initcall_of_isOk; trivial)]
  rw [lookup_insert' (by apply isOk_initcall_of_isOk; trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_insert, setStore_insert, setStore_initcall, setStore_same]

/--
  Closed form for `validator_assert_enum_LegState(v)` when `v` IS a valid
  `LegState` (`v < 4`): the guard-if is skipped and the call is a no-op.
-/
lemma validator_call_ok
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {v : Literal} (hv : v < 4) :
    execCall (fuel+1) validator_assert_enum_LegState [] (Ok evm store, [v])
      = Ok evm store := by
  unfold execCall call validator_assert_enum_LegState
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, nil, If']
  simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMLt']
  simp only [multifill_cons, multifill_nil]
  rw [lookup_initcall_1]
  rw [lookup_insert' (by apply isOk_initcall_of_isOk; trivial)]
  rw [EVMIszero']
  simp only [head', List.head!]
  rw [show fromBool (v < 4) = (1 : UInt256) by
        rw [decide_eq_true hv]; rfl]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) by decide]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  simp only [overwrite?_of_Ok]
  rw [reviveJump_insert (by apply isOk_initcall_of_isOk; trivial)]
  rw [setStore_insert, setStore_initcall, setStore_same]

/--
  Closed form for `abi_encode_enum_LegState(v, pos)` when `v < 4`: skips the
  validity guard and stores `v` at `pos`; no returns.
-/
lemma encode_enum_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {v pos : Literal} (hv : v < 4) :
    execCall (fuel+1) abi_encode_enum_LegState [] (Ok evm store, [v, pos])
      = (Ok evm store).setEvm (evm.mstore pos v) := by
  unfold execCall call abi_encode_enum_LegState
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, nil, If']
  simp only [LetPrimCall', ExprStmtPrimCall', evalArgs, evalTail, cons', head',
             reverse', multifill', PrimCall', Lit', Var', execPrimCall,
             evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMLt']
  simp only [multifill_cons, multifill_nil]
  rw [lookup_initcall_1]
  rw [lookup_insert' (by apply isOk_initcall_of_isOk; trivial)]
  rw [EVMIszero']
  simp only [head', List.head!]
  rw [show fromBool (v < 4) = (1 : UInt256) by
        rw [decide_eq_true hv]; rfl]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) by decide]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  -- the trailing `mstore(pos, value)`
  simp only [ExprStmtPrimCall', evalArgs, evalTail, cons', head', reverse',
             multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMMstore']
  rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
  rw [lookup_initcall_2 (by decide), lookup_initcall_1]
  have hevm : (initcall ["value", "pos"] [v, pos] (Ok evm store)).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  simp only [evm_insert]
  rw [hevm]
  have hok₀ : isOk ((Ok evm store)☎️⟦["value", "pos"], [v, pos]⟧) :=
    isOk_initcall_of_isOk trivial
  have hin_ok : isOk (((Ok evm store)☎️⟦["value", "pos"], [v, pos]⟧⟦"split_expr_0" ↦ 1⟧).setEvm
      (evm.mstore pos v)) := by
    rw [isOk_setEvm, isOk_insert]; exact hok₀
  rw [reviveJump_of_isOk hin_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = evm.mstore pos v := by
    have h := congrArg State.evm hi
    rw [evm_setEvm_of_isOk (by rw [isOk_insert]; exact hok₀)] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]
  rfl

/--
  Closed form for the revert-payload encoder
  `abi_encode_bytes32_bytes32_enum_LegState(v0, v1, v2)` when `v2 < 4`:
  `tail := 100; mstore(4, v0); mstore(36, v1); abi_encode_enum_LegState(v2, 68)`.
  Pure memory effect; returns `100`.
-/
lemma encode_err_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {v0 v1 v2 : Literal}
    {t : Identifier} (hv : v2 < 4) :
    execCall (fuel+1) abi_encode_bytes32_bytes32_enum_LegState [t]
        (Ok evm store, [v0, v1, v2])
      = Ok (((evm.mstore 4 v0).mstore 36 v1).mstore 68 v2) (store.insert t 100) := by
  unfold execCall call abi_encode_bytes32_bytes32_enum_LegState
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, cons, nil]
  simp only [LetEq', Assign', ExprStmtPrimCall', ExprStmtCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMstore']
  simp only [multifill_cons, multifill_nil]
  -- the initcall state and the `tail := 100` insert
  have hok0 : isOk ((Ok evm store)☎️⟦["value0", "value1", "value2"], [v0, v1, v2]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["value0", "value1", "value2"], [v0, v1, v2]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hok1 : isOk ((Ok evm store)☎️⟦["value0", "value1", "value2"], [v0, v1, v2]⟧⟦"tail" ↦ 100⟧) := by
    rw [isOk_insert]; exact hok0
  -- resolve the three parameter lookups (innermost occurrences first)
  have hv0l : ((Ok evm store)☎️⟦["value0", "value1", "value2"], [v0, v1, v2]⟧⟦"tail" ↦ 100⟧)["value0"]!!
      = v0 := by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_initcall_1
  rw [hv0l]
  simp only [evm_insert]
  rw [hevm0]
  -- the state after the first mstore
  have hok2 : isOk (((Ok evm store)☎️⟦["value0", "value1", "value2"], [v0, v1, v2]⟧⟦"tail" ↦ 100⟧).setEvm
      (evm.mstore 4 v0)) := by
    rw [isOk_setEvm]; exact hok1
  have hv1l : (((Ok evm store)☎️⟦["value0", "value1", "value2"], [v0, v1, v2]⟧⟦"tail" ↦ 100⟧).setEvm
      (evm.mstore 4 v0))["value1"]!! = v1 := by
    rw [lookup_setEvm_of_isOk hok1, lookup_insert_of_ne (by decide)]
    exact lookup_initcall_2 (by decide)
  rw [hv1l]
  rw [evm_setEvm_of_isOk hok1]
  -- the state after the second mstore
  have hok3 : isOk ((((Ok evm store)☎️⟦["value0", "value1", "value2"], [v0, v1, v2]⟧⟦"tail" ↦ 100⟧).setEvm
      (evm.mstore 4 v0)).setEvm ((evm.mstore 4 v0).mstore 36 v1)) := by
    rw [isOk_setEvm]; exact hok2
  have hv2l : ((((Ok evm store)☎️⟦["value0", "value1", "value2"], [v0, v1, v2]⟧⟦"tail" ↦ 100⟧).setEvm
      (evm.mstore 4 v0)).setEvm ((evm.mstore 4 v0).mstore 36 v1))["value2"]!! = v2 := by
    rw [lookup_setEvm_of_isOk hok2, lookup_setEvm_of_isOk hok1,
        lookup_insert_of_ne (by decide)]
    exact lookup_initcall_3 (by decide) (by decide)
  rw [hv2l]
  -- the `tail` binding survives to the inner-call input state
  have htail : ((((Ok evm store)☎️⟦["value0", "value1", "value2"], [v0, v1, v2]⟧⟦"tail" ↦ 100⟧).setEvm
      (evm.mstore 4 v0)).setEvm ((evm.mstore 4 v0).mstore 36 v1))["tail"]!! = 100 := by
    rw [lookup_setEvm_of_isOk hok2, lookup_setEvm_of_isOk hok1]
    exact lookup_insert' hok0
  -- expose the inner-call input as a literal `Ok` state
  obtain ⟨e3, σ3, h3⟩ := State_of_isOk hok3
  have he3 : e3 = (evm.mstore 4 v0).mstore 36 v1 := by
    have h := congrArg State.evm h3
    rw [evm_setEvm_of_isOk hok2] at h
    exact h.symm
  rw [h3] at htail ⊢
  rw [encode_enum_call hv]
  -- rets lookup on the inner-call result
  rw [lookup_setEvm_of_isOk (by trivial), htail]
  -- peel the call wrappers
  have hin_ok : isOk ((Ok e3 σ3).setEvm (e3.mstore 68 v2)) := by
    rw [isOk_setEvm]; trivial
  rw [reviveJump_of_isOk hin_ok]
  simp only [overwrite?_of_Ok]
  rw [show (Ok e3 σ3).setEvm (e3.mstore 68 v2) = Ok (e3.mstore 68 v2) σ3 from rfl]
  rw [setStore_ok]
  simp only [insert_Ok]
  rw [he3]

/-! ## The CHECK half: a non-`Revertable` leg reverts the claim;
`Revertable(2)` passes -/

/--
  Closed form of the CHECK block `block_5412558363375237105`:
      _5            := read_from_storage_split_offset_enum_LegState(split_expr_21)
      validator_assert_enum_LegState(_5)
      split_expr_22 := eq(_5, 2)
  Provided the stored byte is a valid `LegState` (`< 4`), the block is pure:
  it binds `_5` to the leg byte and `split_expr_22` to the `Revertable` test.
-/
lemma check_block_state
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slot : Literal}
    (hslot : (Ok evm store)["split_expr_21"]!! = slot)
    (hvalid : Fin.land (evm.sload slot) 255 < 4) :
    exec (fuel+1) block_5412558363375237105 (Ok evm store)
      = Ok evm ((store.insert "_5" (Fin.land (evm.sload slot) 255)).insert
          "split_expr_22" (fromBool (Fin.land (evm.sload slot) 255 = 2))) := by
  unfold block_5412558363375237105
  -- statement 1: _5 := read(...)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append]
  rw [hslot, read_legstate_call_state]
  -- statement 2: validator_assert_enum_LegState(_5)   (no-op given hvalid)
  rw [cons, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             multifill_cons, multifill_nil]
  have hlk5 : ((Ok evm store)⟦"_5" ↦ Fin.land (evm.sload slot) 255⟧)["_5"]!!
      = Fin.land (evm.sload slot) 255 := lookup_insert' (by trivial)
  rw [hlk5, insert_Ok, validator_call_ok hvalid]
  -- statement 3: split_expr_22 := eq(_5, 2)
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             multifill_cons, multifill_nil, EVMEq']
  have hlk5' : (Ok evm (Finmap.insert "_5" (Fin.land (evm.sload slot) 255) store))["_5"]!!
      = Fin.land (evm.sload slot) 255 := by
    rw [← insert_Ok]; exact lookup_insert' (by trivial)
  rw [hlk5']
  simp only [insert_Ok]

/--
  The guard-if `if_880639588767859599` REVERTS when its guard is `0` (the leg
  is not `Revertable`) and the leg byte `_5` is a valid `LegState`:
      if iszero(split_expr_22) {
        split_expr_23 := shl(224, …)
        mstore(0, split_expr_23)
        split_expr_24 := abi_encode_bytes32_bytes32_enum_LegState(var__flowId, expr, _5)
        revert(0, split_expr_24)
      }
-/
lemma guard_if_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {s₉ : State}
    (hz : (Ok evm store)["split_expr_22"]!! = 0)
    (h5 : (Ok evm store)["_5"]!! < 4)
    (hexec : exec (fuel+1) if_880639588767859599 (Ok evm store) = s₉) :
    s₉.evm.reverted = true := by
  rw [← hexec]
  unfold if_880639588767859599
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append]
  rw [EVMIszero']
  simp only [head', List.head!]
  rw [hz]
  rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) by decide]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- body: shl / mstore / encode_err / revert
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             multifill_cons, multifill_nil, EVMShl']
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             multifill_cons, multifill_nil, EVMMstore']
  have hlk23 : ((Ok evm store)⟦"split_expr_23" ↦ Fin.shiftLeft 2203461383 224⟧)["split_expr_23"]!!
      = Fin.shiftLeft 2203461383 224 := lookup_insert' (by trivial)
  rw [hlk23]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil]
  -- resolve the encoder's three symbolic-arg lookups through insert + setEvm
  have hok1 : isOk ((Ok evm store)⟦"split_expr_23" ↦ Fin.shiftLeft 2203461383 224⟧) := by
    rw [isOk_insert]; trivial
  have hargs : ∀ k : Identifier, k ≠ "split_expr_23" →
      (((Ok evm store)⟦"split_expr_23" ↦ Fin.shiftLeft 2203461383 224⟧).setEvm
        (((Ok evm store)⟦"split_expr_23" ↦ Fin.shiftLeft 2203461383 224⟧).evm.mstore 0
          (Fin.shiftLeft 2203461383 224)))[k]!! = (Ok evm store)[k]!! := by
    intro k hk
    rw [lookup_setEvm_of_isOk hok1, lookup_insert_of_ne hk]
  rw [hargs "_5" (by decide), hargs "expr" (by decide), hargs "var__flowId" (by decide)]
  -- expose the encoder input as a literal `Ok` state and run the closed form
  have hok2 : isOk (((Ok evm store)⟦"split_expr_23" ↦ Fin.shiftLeft 2203461383 224⟧).setEvm
      (((Ok evm store)⟦"split_expr_23" ↦ Fin.shiftLeft 2203461383 224⟧).evm.mstore 0
        (Fin.shiftLeft 2203461383 224))) := by
    rw [isOk_setEvm]; exact hok1
  obtain ⟨e1, σ1, h1⟩ := State_of_isOk hok2
  rw [h1, encode_err_call h5]
  -- the final `revert(0, split_expr_24)`
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             multifill_cons, multifill_nil, EVMRevert']
  have hlk24 : (Ok (((e1.mstore 4 ((Ok evm store)["var__flowId"]!!)).mstore 36
        ((Ok evm store)["expr"]!!)).mstore 68 ((Ok evm store)["_5"]!!))
      (Finmap.insert "split_expr_24" 100 σ1))["split_expr_24"]!! = 100 := by
    rw [← insert_Ok]; exact lookup_insert' (by trivial)
  rw [hlk24]
  rfl

/--
  The guard-if `if_880639588767859599` FALLS THROUGH with the state unchanged
  when its guard `split_expr_22` is `1` — the leg IS `Revertable(2)`.
-/
lemma guard_if_passes
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (h1 : (Ok evm store)["split_expr_22"]!! = 1) :
    exec (fuel+1) if_880639588767859599 (Ok evm store) = Ok evm store := by
  unfold if_880639588767859599
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append]
  rw [EVMIszero']
  simp only [head', List.head!]
  rw [h1]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) by decide]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]

/-- **CHECK-side state predicate.** Running the CHECK block + guard-if of
`claimRefund` from a state whose stored leg byte (at the slot bound to
`split_expr_21`) is a valid `LegState` other than `Revertable(2)` ends with
`reverted = true`.  Instances: `Unset(0)`, `Committed(1)`, `Reverted(3)`. -/
theorem refund_check_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {s_mid s₉ : State} {slot : Literal}
    (hslot : (Ok evm store)["split_expr_21"]!! = slot)
    (hvalid : Fin.land (evm.sload slot) 255 < 4)
    (hnot2 : Fin.land (evm.sload slot) 255 ≠ 2)
    (hcheck : exec (fuel+1) block_5412558363375237105 (Ok evm store) = s_mid)
    (hif : exec (fuel+1) if_880639588767859599 s_mid = s₉) :
    s₉.evm.reverted = true := by
  rw [check_block_state hslot hvalid] at hcheck
  subst hcheck
  refine guard_if_reverts ?_ ?_ hif
  · -- the guard variable is 0: the leg is not Revertable
    have h22 : (Ok evm ((store.insert "_5" (Fin.land (evm.sload slot) 255)).insert
        "split_expr_22" (fromBool (Fin.land (evm.sload slot) 255 = 2))))["split_expr_22"]!!
        = fromBool (Fin.land (evm.sload slot) 255 = 2) := by
      rw [← insert_Ok]; exact lookup_insert' (by trivial)
    rw [h22]
    rw [show fromBool (Fin.land (evm.sload slot) 255 = 2) = (0 : UInt256) from by
      rw [decide_eq_false hnot2]; rfl]
  · -- the leg byte is a valid LegState
    have h5 : (Ok evm ((store.insert "_5" (Fin.land (evm.sload slot) 255)).insert
        "split_expr_22" (fromBool (Fin.land (evm.sload slot) 255 = 2))))["_5"]!!
        = Fin.land (evm.sload slot) 255 := by
      rw [← insert_Ok, lookup_insert_of_ne (by decide), ← insert_Ok]
      exact lookup_insert' (by trivial)
    rw [h5]
    exact hvalid

/-- **CHECK-side PASS.** Running the CHECK block + guard-if of `claimRefund`
from a state whose stored leg byte (at the slot bound to `split_expr_21`) is
EXACTLY `Revertable(2)` falls through: the guard is satisfied and the state is
unchanged up to the two scratch binds (`_5`, `split_expr_22`).  In particular
no revert happens and the claim proceeds to the SET + payout —
`authorizeRefund`'s mark is precisely what unlocks it. -/
theorem refund_check_passes
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {s_mid s₉ : State} {slot : Literal}
    (hslot : (Ok evm store)["split_expr_21"]!! = slot)
    (h2 : Fin.land (evm.sload slot) 255 = 2)
    (hcheck : exec (fuel+1) block_5412558363375237105 (Ok evm store) = s_mid)
    (hif : exec (fuel+1) if_880639588767859599 s_mid = s₉) :
    s₉ = Ok evm ((store.insert "_5" (Fin.land (evm.sload slot) 255)).insert
          "split_expr_22" 1) := by
  rw [check_block_state hslot (by rw [h2]; decide)] at hcheck
  subst hcheck
  rw [show fromBool (Fin.land (evm.sload slot) 255 = 2) = (1 : UInt256) from by
        rw [decide_eq_true h2]; rfl] at hif
  rw [← hif]
  exact guard_if_passes (by rw [← insert_Ok]; exact lookup_insert' (by trivial))

/-! ## The SET (mark) halves: `authorizeRefund` stores `Revertable(2)`,
`claimRefund` stores `Reverted(3)` -/

private lemma ne_c0 : ("cleaned" : Identifier) ≠ "split_expr_0" := by decide
private lemma ne_slc : ("slot" : Identifier) ≠ "cleaned" := by decide

/--
  Closed form for the AUTHORIZE-side mark
  `update_storage_value_offset_enum_LegState_to_enum_LegState(slot)` (the base
  helper, called by `authorizeRefund`): reads `slot`, clears the low byte, ORs
  in `Revertable(2)`, stores it back.
-/
lemma update_storage_writes_revertable
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slot : Literal} :
    execCall (fuel+1) update_storage_value_offset_enum_LegState_to_enum_LegState []
        (Ok evm store, [slot])
      = (Ok evm store).setEvm
          (evm.sstore slot (Fin.lor (Fin.land (evm.sload slot) (Clear.UInt256.lnot 255)) 2)) := by
  unfold execCall call update_storage_value_offset_enum_LegState_to_enum_LegState
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  simp only [cons, nil]
  simp only [LetEq', Assign', LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMSload', EVMNot', EVMAnd', EVMOr', EVMSstore']
  simp only [multifill_cons, multifill_nil]
  -- abbreviations; generalize the computed values to keep terms small.
  generalize hsv : evm.sload slot = sv
  set m255 := Clear.UInt256.lnot 255 with hm255
  set v2 := Fin.land sv m255 with hv2
  set v3 := Fin.lor v2 2 with hv3
  set B := (Ok evm store)☎️⟦["slot"], [slot]⟧⟦"cleaned" ↦ 0⟧⟦"cleaned" ↦ 0⟧ with hB
  have hok_ic : isOk ((Ok evm store)☎️⟦["slot"], [slot]⟧) := isOk_initcall_of_isOk trivial
  have hokB : isOk B := by
    rw [hB, isOk_insert, isOk_insert]; exact hok_ic
  have hBevm : B.evm = evm := by
    rw [hB]
    simp only [evm_insert]
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hBslot : B["slot"]!! = slot := by
    rw [hB, lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact lookup_initcall_1
  rw [hBevm, hBslot, hsv]
  have hok0 : isOk (B⟦"split_expr_0" ↦ sv⟧) := isOk_insert.mpr hokB
  have hok1 : isOk (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧) := isOk_insert.mpr hok0
  have hok2 : isOk (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧) :=
    isOk_insert.mpr hok1
  have hok3 : isOk (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧) :=
    isOk_insert.mpr hok2
  have l0 : (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧)["split_expr_0"]!! = sv := by
    rw [lookup_insert_of_ne (by decide), lookup_insert' hokB]
  have l1 : (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧)["split_expr_1"]!! = m255 :=
    lookup_insert' hok0
  rw [l0, l1, ← hv2]
  have l2 : (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧)["split_expr_2"]!! = v2 :=
    lookup_insert' hok1
  rw [l2, ← hv3]
  have lslot : (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧)["slot"]!! = slot := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
        lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact hBslot
  have l3 : (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧)["split_expr_3"]!! = v3 :=
    lookup_insert' hok2
  rw [lslot, l3]
  rw [show (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧).evm = evm from by
        simp only [evm_insert]; exact hBevm]
  have hinner_ok : isOk ((B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧)🇪⟦evm.sstore slot v3⟧) := by
    rw [isOk_setEvm]; exact hok3
  rw [reviveJump_of_isOk hinner_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hinner_ok
  have hi_evm : ei = evm.sstore slot v3 := by
    have h := congrArg State.evm hi
    rw [evm_setEvm_of_isOk hok3] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]
  rfl

/--
  Closed form for the CLAIM-side mark
  `update_storage_value_offset_enum_LegState_to_enum_LegState_7877(slot)`
  (called by `claimRefund` after the `Revertable` guard): reads `slot`, clears
  the low byte, ORs in `Reverted(3)`, stores it back.
-/
lemma update_storage_7877_writes_reverted
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slot : Literal} :
    execCall (fuel+1) update_storage_value_offset_enum_LegState_to_enum_LegState_7877 []
        (Ok evm store, [slot])
      = (Ok evm store).setEvm
          (evm.sstore slot (Fin.lor (Fin.land (evm.sload slot) (Clear.UInt256.lnot 255)) 3)) := by
  unfold execCall call update_storage_value_offset_enum_LegState_to_enum_LegState_7877
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  simp only [cons, nil]
  simp only [LetEq', Assign', LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMSload', EVMNot', EVMAnd', EVMOr', EVMSstore']
  simp only [multifill_cons, multifill_nil]
  -- abbreviations; generalize the computed values to keep terms small.
  generalize hsv : evm.sload slot = sv
  set m255 := Clear.UInt256.lnot 255 with hm255
  set v2 := Fin.land sv m255 with hv2
  set v3 := Fin.lor v2 3 with hv3
  set B := (Ok evm store)☎️⟦["slot"], [slot]⟧⟦"cleaned" ↦ 0⟧⟦"cleaned" ↦ 0⟧ with hB
  have hok_ic : isOk ((Ok evm store)☎️⟦["slot"], [slot]⟧) := isOk_initcall_of_isOk trivial
  have hokB : isOk B := by
    rw [hB, isOk_insert, isOk_insert]; exact hok_ic
  have hBevm : B.evm = evm := by
    rw [hB]
    simp only [evm_insert]
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hBslot : B["slot"]!! = slot := by
    rw [hB, lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact lookup_initcall_1
  rw [hBevm, hBslot, hsv]
  have hok0 : isOk (B⟦"split_expr_0" ↦ sv⟧) := isOk_insert.mpr hokB
  have hok1 : isOk (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧) := isOk_insert.mpr hok0
  have hok2 : isOk (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧) :=
    isOk_insert.mpr hok1
  have hok3 : isOk (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧) :=
    isOk_insert.mpr hok2
  have l0 : (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧)["split_expr_0"]!! = sv := by
    rw [lookup_insert_of_ne (by decide), lookup_insert' hokB]
  have l1 : (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧)["split_expr_1"]!! = m255 :=
    lookup_insert' hok0
  rw [l0, l1, ← hv2]
  have l2 : (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧)["split_expr_2"]!! = v2 :=
    lookup_insert' hok1
  rw [l2, ← hv3]
  have lslot : (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧)["slot"]!! = slot := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
        lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact hBslot
  have l3 : (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧)["split_expr_3"]!! = v3 :=
    lookup_insert' hok2
  rw [lslot, l3]
  rw [show (B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧).evm = evm from by
        simp only [evm_insert]; exact hBevm]
  have hinner_ok : isOk ((B⟦"split_expr_0" ↦ sv⟧⟦"split_expr_1" ↦ m255⟧⟦"split_expr_2" ↦ v2⟧⟦"split_expr_3" ↦ v3⟧)🇪⟦evm.sstore slot v3⟧) := by
    rw [isOk_setEvm]; exact hok3
  rw [reviveJump_of_isOk hinner_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hinner_ok
  have hi_evm : ei = evm.sstore slot v3 := by
    have h := congrArg State.evm hi
    rw [evm_setEvm_of_isOk hok3] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]
  rfl

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
`(x &&& ~255) ||| 3`, has low byte `and(_,255) = 3` — i.e. exactly
`LegState.Reverted`. -/
theorem fin_mask_three (x : UInt256) :
    Fin.land (Fin.lor (Fin.land x (Clear.UInt256.lnot 255)) 3) 255 = 3 := by
  apply Fin.ext
  rcases x with ⟨a, ha⟩
  show Nat.land (Nat.lor (Nat.land a (UInt256.size - 256) % UInt256.size) 3 % UInt256.size) 255 % UInt256.size = 3
  have hsz : UInt256.size = 2^256 := by norm_num
  rw [hsz]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have key : ∀ z : ℕ, (z % 2^256).testBit i = z.testBit i := fun z => by
      rw [Nat.testBit_mod_two_pow]; simp [show i < 256 by omega]
    rw [key]
    show ((Nat.lor (Nat.land a (2^256 - 256) % 2^256) 3 % 2^256) &&& 255).testBit i = (3:ℕ).testBit i
    rw [show ∀ p q : ℕ, Nat.land p q = p &&& q from fun _ _ => rfl,
        show ∀ p q : ℕ, Nat.lor p q = p ||| q from fun _ _ => rfl]
    rw [Nat.testBit_land]
    rw [key ((a &&& (2^256 - 256)) % 2^256 ||| 3)]
    rw [Nat.testBit_lor]
    rw [key (a &&& (2^256 - 256))]
    rw [Nat.testBit_land]
    have hbmask : (2^256 - 256 : ℕ).testBit i = false := by
      apply low_bit_zero _ i hi; decide
    rw [hbmask, Bool.and_false, Bool.false_or, Bool.and_comm]
    have hb255 : (255:ℕ).testBit i = true := by interval_cases i <;> rfl
    rw [hb255, Bool.true_and]
  · have hge : 8 ≤ i := by omega
    have key : (Nat.land (Nat.lor (Nat.land a (2^256-256) % 2^256) 3 % 2^256) 255 % 2^256).testBit i = false := by
      rw [Nat.testBit_mod_two_pow]
      by_cases hi256 : i < 256
      · simp only [hi256, decide_True, Bool.true_and]
        show ((Nat.lor (Nat.land a (2^256-256) % 2^256) 3 % 2^256) &&& 255).testBit i = false
        rw [Nat.testBit_land, tb255_lt i hge, Bool.and_false]
      · simp [hi256]
    rw [key]
    have hb3 : (3:ℕ).testBit i = false :=
      Nat.testBit_lt_two_pow (by calc (3:ℕ) < 2^8 := by norm_num
        _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) hge)
    rw [hb3]

/-- The claim-side SET value is nonzero (its low byte is `3`). -/
theorem fin_mask_three_ne_zero (x : UInt256) :
    Fin.lor (Fin.land x (Clear.UInt256.lnot 255)) 3 ≠ 0 := by
  intro h
  have := fin_mask_three x
  rw [h] at this
  simp only [Fin.land] at this
  exact absurd this (by decide)

/-- **Pure low-byte lemma (authorize side).** The value written by the
authorize-side mark, `(x &&& ~255) ||| 2`, has low byte `and(_,255) = 2` —
i.e. exactly `LegState.Revertable`. -/
theorem fin_mask_two (x : UInt256) :
    Fin.land (Fin.lor (Fin.land x (Clear.UInt256.lnot 255)) 2) 255 = 2 := by
  apply Fin.ext
  rcases x with ⟨a, ha⟩
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

/-- The authorize-side SET value is nonzero (its low byte is `2`). -/
theorem fin_mask_two_ne_zero (x : UInt256) :
    Fin.lor (Fin.land x (Clear.UInt256.lnot 255)) 2 ≠ 0 := by
  intro h
  have := fin_mask_two x
  rw [h] at this
  simp only [Fin.land] at this
  exact absurd this (by decide)

/-- Re-reading the slot just written returns the stored value (contract account
exists, value nonzero — the storage model returns `0` for a missing account). -/
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

/-- **The claim-side SET sets `Reverted`.** After the `_7877` write helper runs
at `slot`, the stored leg byte is exactly `3 = LegState.Reverted`. -/
theorem update_storage_sets_reverted_byte
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slot : Literal} {s' : State}
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome)
    (hexec : execCall (fuel+1) update_storage_value_offset_enum_LegState_to_enum_LegState_7877 []
                (Ok evm store, [slot]) = s') :
    Fin.land (s'.evm.sload slot) 255 = 3 := by
  rw [← hexec, update_storage_7877_writes_reverted]
  rw [evm_setEvm_of_isOk (by trivial : isOk (Ok evm store))]
  rw [sload_sstore_self_of_nonzero evm slot _ (fin_mask_three_ne_zero (evm.sload slot)) hacc]
  exact fin_mask_three (evm.sload slot)

/-- **The authorize-side SET sets `Revertable`.** After the base write helper
(`authorizeRefund`'s mark) runs at `slot`, the stored leg byte is exactly
`2 = LegState.Revertable`. -/
theorem update_storage_sets_revertable_byte
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slot : Literal} {s' : State}
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome)
    (hexec : execCall (fuel+1) update_storage_value_offset_enum_LegState_to_enum_LegState []
                (Ok evm store, [slot]) = s') :
    Fin.land (s'.evm.sload slot) 255 = 2 := by
  rw [← hexec, update_storage_writes_revertable]
  rw [evm_setEvm_of_isOk (by trivial : isOk (Ok evm store))]
  rw [sload_sstore_self_of_nonzero evm slot _ (fin_mask_two_ne_zero (evm.sload slot)) hacc]
  exact fin_mask_two (evm.sload slot)

/-! ## END-TO-END: the two-step machine -/

/-- **THE FORWARD STEP: authorize unlocks the claim.** Run `authorizeRefund`\'s
mark at `slot` (the base helper — `Committed → Revertable(2)`); then run
`claimRefund`\'s CHECK block + guard-if with `split_expr_21 ↦ slot` on the
post-write evm.  The guard PASSES: the state falls through unreverted (only the
two scratch binds are added), and the claim proceeds to the `Reverted(3)` mark
and payout. -/
theorem claim_after_authorize_passes
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    {slot : Literal} {s_set s_mid s₉ : State}
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome)
    (hset_exec : execCall (fuel+1) update_storage_value_offset_enum_LegState_to_enum_LegState []
                    (Ok evm store, [slot]) = s_set)
    (hcheck_exec : exec (fuel+1) block_5412558363375237105
                      ((Ok s_set.evm store)⟦"split_expr_21" ↦ slot⟧) = s_mid)
    (hif_exec : exec (fuel+1) if_880639588767859599 s_mid = s₉) :
    s₉ = Ok s_set.evm (((store.insert "split_expr_21" slot).insert "_5"
          (Fin.land (s_set.evm.sload slot) 255)).insert "split_expr_22" 1) := by
  have hbyte : Fin.land (s_set.evm.sload slot) 255 = 2 :=
    update_storage_sets_revertable_byte hacc hset_exec
  rw [insert_Ok] at hcheck_exec
  have hslot : (Ok s_set.evm (store.insert "split_expr_21" slot))["split_expr_21"]!! = slot := by
    rw [← insert_Ok]; exact lookup_insert' (by trivial)
  exact refund_check_passes hslot hbyte hcheck_exec hif_exec

/-- **NO DOUBLE REFUND (leg-level anti-double-mint).** Run the `claimRefund`
SET write at `slot` (the `_7877` helper — marking the leg `Reverted(3)`); then
re-run `claimRefund`\'s CHECK block + guard-if with `split_expr_21 ↦ slot` on
the post-write evm.  The re-read is `3 ≠ 2`, so the re-claim ends
`reverted = true`: the leg state machine admits at most one refund per leg.
Combined with `refund_check_reverts`\'s other instances (`Unset`, `Committed`),
`claimRefund` can pay out ONLY a leg in state `Revertable` — i.e. only after
`authorizeRefund`\'s timeout proof, and at most once.

Hypothesis `hacc` (the contract\'s own account exists) is the standard deployed-
contract fact; the shared `slot` variable is the CHECK = SET slot identification
(both are the same 2-level keccak accessor chain over `(flowId, bundleHash)` —
discharged at statement level by `claim_check_set_slots_eq` below). -/
theorem reclaim_after_refund_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    {slot : Literal} {s_set s_mid s₉ : State}
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome)
    (hset_exec : execCall (fuel+1) update_storage_value_offset_enum_LegState_to_enum_LegState_7877 []
                    (Ok evm store, [slot]) = s_set)
    (hcheck_exec : exec (fuel+1) block_5412558363375237105
                      ((Ok s_set.evm store)⟦"split_expr_21" ↦ slot⟧) = s_mid)
    (hif_exec : exec (fuel+1) if_880639588767859599 s_mid = s₉) :
    s₉.evm.reverted = true := by
  have hbyte : Fin.land (s_set.evm.sload slot) 255 = 3 :=
    update_storage_sets_reverted_byte hacc hset_exec
  rw [insert_Ok] at hcheck_exec
  have hslot : (Ok s_set.evm (store.insert "split_expr_21" slot))["split_expr_21"]!! = slot := by
    rw [← insert_Ok]; exact lookup_insert' (by trivial)
  exact refund_check_reverts hslot
    (by rw [hbyte]; decide) (by rw [hbyte]; decide) hcheck_exec hif_exec

/-! ## SLOT-EQUALITY — the slot CHECKED equals the slot SET

`claimRefund` computes `_state[flowId][bundleHash]` TWICE — once for the CHECK
(`split_expr_20/21`) and once for the SET (`split_expr_25/26`) — via the same
2-level keccak accessor chain (level 1: base slot `0`; level 2: the level-1
slot).  By `Clear.KeccakDeterminism.accessor_chain2_deterministic` the re-run
replays the cached keccak slots, so the two computations agree.  This
discharges the shared-`slot` identification of `reclaim_after_refund_reverts`
at statement level (2-level analog of the L1Nullifier `check_set_slots_eq`). -/

open Clear.KeccakDeterminism

/-- The keccak PRIMOP in `keccakOut` form. -/
lemma primCall_keccakOut {s : State} {a b : Literal} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (keccakOut s.evm a b).2, [(keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

/--
  Closed form of the level-1 accessor
  `mapping_…_7848(key)` (`mstore(0, key); mstore(32, 0); dataSlot := keccak256(0, 64)`):
  one `accOut` step at `(key, 0)`.
-/
lemma mapping_legstate_7848_call_acc
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {key : Literal} {v : Identifier} :
    execCall (fuel+1) mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7848
        [v] (Ok evm store, [key])
      = Ok (accOut evm key 0).2 (store.insert v (accOut evm key 0).1) := by
  unfold execCall call mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7848
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
  have hok₀ : isOk ((Ok evm store)☎️⟦["key"], [key]⟧) := isOk_initcall_of_isOk trivial
  have hevm₀ : ((Ok evm store)☎️⟦["key"], [key]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hkey : ((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!! = key := lookup_initcall_1
  set host := (((Ok evm store)☎️⟦["key"], [key]⟧)
      🇪⟦((Ok evm store)☎️⟦["key"], [key]⟧).evm.mstore 0
          (((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!!)⟧)
      🇪⟦(((Ok evm store)☎️⟦["key"], [key]⟧)
          🇪⟦((Ok evm store)☎️⟦["key"], [key]⟧).evm.mstore 0
              (((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!!)⟧).evm.mstore 32 0⟧
      with hhost
  have hhost_ok : isOk host := by
    rw [hhost, isOk_setEvm, isOk_setEvm]; exact hok₀
  have hhost_evm : host.evm = (evm.mstore 0 key).mstore 32 0 := by
    rw [hhost, evm_setEvm_of_isOk (by rw [isOk_setEvm]; exact hok₀),
        evm_setEvm_of_isOk hok₀, hevm₀, hkey]
  rw [hhost_evm]
  unfold accOut
  generalize hout : keccakOut ((evm.mstore 0 key).mstore 32 0) 0 64 = out
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
  Closed form of the level-2 accessor
  `mapping_…(slot, key)` (`mstore(0, key); mstore(32, slot); dataSlot := keccak256(0, 64)`):
  one `accOut` step at `(key, slot)`.
-/
lemma mapping_legstate_call_acc
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slotArg key : Literal} {v : Identifier} :
    execCall (fuel+1) mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32
        [v] (Ok evm store, [slotArg, key])
      = Ok (accOut evm key slotArg).2 (store.insert v (accOut evm key slotArg).1) := by
  unfold execCall call mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32
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

/-- **SLOT-EQUALITY for `claimRefund`** — `split_expr_26 = split_expr_21`.

Running the 2-level accessor chain twice with the same keys — the CHECK chain
(`split_expr_20/21` over `(var__flowId, expr)`) and the SET chain
(`split_expr_25/26`) — returns the SAME final storage slot, provided the
intervening execution (the read/validator/eq/guard-if success path) (i) left
memory bytes `[64, 95)` unchanged and (ii) dropped no keccak-cache entry, and
(iii) the CHECK chain ended hash-collision-free (A6-style model caveat). -/
theorem claim_check_set_slots_eq
    {evm₀ evmM : EVMState} {st₀ stM : VarStore}
    {f₂₀ f₂₁ f₂₅ f₂₆ : ℕ} {k₁ k₂ b₂₁ b₂₆ : Literal}
    {s₂₀ s₂₁ s₂₅ s₂₆ : State}
    {v₂₀ v₂₁ v₂₅ v₂₆ : Identifier}
    -- CHECK-side chain (split_expr_20/21)
    (h₂₀ : execCall (f₂₀+1)
        mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7848
        [v₂₀] (Ok evm₀ st₀, [k₁]) = s₂₀)
    (h₂₁ : execCall (f₂₁+1)
        mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32
        [v₂₁] (s₂₀, [b₂₁, k₂]) = s₂₁)
    (hb₂₁ : b₂₁ = s₂₀[v₂₀]!!)
    -- frame: the intervening execution (CHECK-chain end → SET-chain start)
    (hmem : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i evmM.machine_state.memory
        = Finmap.lookup i s₂₁.evm.machine_state.memory)
    (hmono : ∀ (I : List UInt256) (w : UInt256),
      Finmap.lookup I s₂₁.evm.keccak_map = some w
        → Finmap.lookup I evmM.keccak_map = some w)
    -- SET-side chain (split_expr_25/26)
    (h₂₅ : execCall (f₂₅+1)
        mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7848
        [v₂₅] (Ok evmM stM, [k₁]) = s₂₅)
    (h₂₆ : execCall (f₂₆+1)
        mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32
        [v₂₆] (s₂₅, [b₂₆, k₂]) = s₂₆)
    (hb₂₆ : b₂₆ = s₂₅[v₂₅]!!)
    -- no keccak-collision fallback on the CHECK side (A6 model caveat)
    (hclean : s₂₁.evm.hash_collision = false) :
    s₂₆[v₂₆]!! = s₂₁[v₂₁]!! := by
  rw [mapping_legstate_7848_call_acc] at h₂₀
  have hs₂₀v : s₂₀[v₂₀]!! = (accOut evm₀ k₁ 0).1 := by
    rw [← h₂₀, ← insert_Ok]; exact lookup_insert' (by trivial)
  rw [hb₂₁, hs₂₀v] at h₂₁
  rw [← h₂₀] at h₂₁
  rw [mapping_legstate_call_acc] at h₂₁
  have hs₂₁v : s₂₁[v₂₁]!! = (accOut (accOut evm₀ k₁ 0).2 k₂ (accOut evm₀ k₁ 0).1).1 := by
    rw [← h₂₁, ← insert_Ok]; exact lookup_insert' (by trivial)
  have hs₂₁evm : s₂₁.evm = (accOut (accOut evm₀ k₁ 0).2 k₂ (accOut evm₀ k₁ 0).1).2 := by
    rw [← h₂₁]; rfl
  rw [mapping_legstate_7848_call_acc] at h₂₅
  have hs₂₅v : s₂₅[v₂₅]!! = (accOut evmM k₁ 0).1 := by
    rw [← h₂₅, ← insert_Ok]; exact lookup_insert' (by trivial)
  rw [hb₂₆, hs₂₅v] at h₂₆
  rw [← h₂₅] at h₂₆
  rw [mapping_legstate_call_acc] at h₂₆
  have hs₂₆v : s₂₆[v₂₆]!! = (accOut (accOut evmM k₁ 0).2 k₂ (accOut evmM k₁ 0).1).1 := by
    rw [← h₂₆, ← insert_Ok]; exact lookup_insert' (by trivial)
  have hdet := accessor_chain2_deterministic
    (σ₀ := evm₀) (σmid := evmM) (k₁ := k₁) (k₂ := k₂) (b := 0)
    (h₅ := rfl) (h₆ := rfl)
    (hmem := by rw [hs₂₁evm] at hmem; exact hmem)
    (hmono := by rw [hs₂₁evm] at hmono; exact hmono)
    (h₁₁ := rfl) (h₁₂ := rfl)
    (hclean := by rw [hs₂₁evm] at hclean; exact hclean)
  rw [hs₂₆v, hs₂₁v]
  exact hdet.2

end

end generated.AtomicFlowManager.AtomicFlowManager
