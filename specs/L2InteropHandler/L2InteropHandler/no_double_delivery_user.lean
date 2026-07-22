import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_leaf_storage_user
import specs.InteropHandler.InteropHandler.no_double_delivery_user

/-
  NO DOUBLE DELIVERY (L2InteropHandler, post-relocation corpus).

  In the new compile `_markFullyExecutedAndRun` is inlined into the
  dispatcher's `executeBundle` branch.  The check-then-set survives verbatim
  at the source level:

  * the STATUS GUARD (src 43:6258:6326) accepts only
    `Unreceived (0)` / `Verified (1)`:

        let expr_11 := iszero(expr_component_14)
        if iszero(expr_11) { _20 := _1  expr_11 := eq(expr_component_14, 1) }

  * the MARK (src 43:6617:6670) writes `FullyExecuted (2)` into the low byte
    of `bundleStatus[bundleHash]` at the protocol-standard mapping slot
    `keccak256(bundleHash ‖ 1)` — BEFORE any bundle call runs (CEI):

        mstore(_1, expr_component_13)   // _1 = 0
        mstore(0x20, 1)
        let slot := keccak256(_1, 64)
        sstore(slot, or(and(sload(slot), not(255)), 2))

  This file proves closed forms of both compiled pieces and composes them
  with the old corpus's pure mask/readback lemmas (`fin_mask_two`,
  `sload_sstore_self`) into `no_double_delivery_guard`: after the mark, the
  re-read status is `2`, and the guard computes `expr_11 = 0` — the require
  reverts with `BundleAlreadyProcessed`.  A bundle executes at most once.

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

/-! ### The compiled pieces, quoted verbatim -/

/-- The status-slot computation of the inlined mark (dispatcher `executeBundle`
branch): `keccak256(bundleHash ‖ 1)`.  `_1` holds the dispatcher-wide zero. -/
private def markBlk1 : Stmt := <s
  {
    mstore(_1, expr_component_13)
    mstore(0x20, 1)
    let slot := keccak256(_1, 64)
    let cleaned := 0
    cleaned := 0
}
>

/-- The status write, fully inlined in this corpus:
`sstore(slot, (old &&& ~255) ||| 2)`. -/
private def markBlk2 : Stmt := <s
  {
    sstore(slot, or(and(sload(slot), not(255)), 2))
}
>

/-- The status guard of `executeBundle`: accept iff the status is
`Unreceived (0)` or `Verified (1)`. -/
private def statusGuard : Stmt := <s
  {
    let expr_11 := iszero(expr_component_14)
    if iszero(expr_11)
    {
        _20 := _1
        expr_11 := eq(expr_component_14, 1)
    }
}
>

/-! ### Closed forms of the mark -/

/-- **Slot block closed form**: the status slot is one `accOut` step at
`(bundleHash, 1)` — the same protocol-standard mapping slot as the old corpus. -/
lemma mark_slot_block
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {bh : Literal}
    (h1 : (Ok evm store)["_1"]!! = 0)
    (hbh : (Ok evm store)["expr_component_13"]!! = bh) :
    exec (fuel+1) markBlk1 (Ok evm store)
      = Ok (accOut evm bh 1).2
          (((store.insert "slot" (accOut evm bh 1).1).insert
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
  simp only [evm_insert, evm_Ok, setEvm_Ok, insert_Ok]
  try simp only [List.head!]
  rw [h1, hbh]
  try rw [h1]
  try rw [lookup_ok_evm _ evm, h1]
  rw [primCall_keccakOut]
  simp only [multifill_cons, multifill_nil, evm_Ok, setEvm_Ok, insert_Ok]
  have halign : keccakOut ((evm.mstore 0 bh).mstore 32 1) 0 64 = accOut evm bh 1 := by
    unfold accOut
    rfl
  try rw [halign]
  try simp only [halign]
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]

/-- **Write block closed form**: the (nested) write stores
`(old &&& ~255) ||| 2` at the status slot, leaving the store untouched. -/
lemma mark_write_block
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {d : Literal}
    (hd : (Ok evm store)["slot"]!! = d) :
    exec (fuel+1) markBlk2 (Ok evm store)
      = Ok (evm.sstore d (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 2))
          store := by
  unfold markBlk2
  simp only [cons, nil]
  rw [ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil,
             EVMSload', EVMNot', EVMAnd', EVMOr', EVMSstore', evm_Ok, setEvm_Ok]
  try simp only [List.head!]
  rw [hd]
  try rw [hd]
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]

/-! ### The status guard: pass on 0/1, block otherwise -/

/-- **Fresh bundle passes**: status `Unreceived (0)` computes `expr_11 = 1`. -/
theorem status_fresh_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hs : (Ok evm store)["expr_component_14"]!! = 0) :
    ∃ σ' : VarStore,
      exec (fuel+1) statusGuard (Ok evm store) = Ok evm σ'
      ∧ (Ok evm σ')["expr_11"]!! = 1 := by
  unfold statusGuard
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMIszero', insert_Ok]
  try simp only [List.head!]
  rw [hs]
  rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  -- if iszero(expr_11) with expr_11 = 1 — skip
  rw [cons, nil, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  try simp only [lookup_insert_self_fin]
  try simp only [List.head!]
  try simp only [reduceIte]
  refine ⟨_, rfl, ?_⟩
  exact lookup_insert_self_fin

/-- **Verified bundle passes**: status `Verified (1)` computes `expr_11 = 1`
through the fallback arm. -/
theorem status_verified_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hs : (Ok evm store)["expr_component_14"]!! = 1) :
    ∃ σ' : VarStore,
      exec (fuel+1) statusGuard (Ok evm store) = Ok evm σ'
      ∧ (Ok evm σ')["expr_11"]!! = 1 := by
  unfold statusGuard
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMIszero', insert_Ok]
  try simp only [List.head!]
  rw [hs]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  -- if iszero(expr_11) with expr_11 = 0 — enter
  rw [cons, nil, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  try simp only [lookup_insert_self_fin]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_pos (by decide : fromBool (decide True) ≠ (0 : UInt256))]
  -- _20 := _1
  rw [cons, Assign']
  simp only [Var', insert_Ok]
  -- expr_11 := eq(expr_component_14, 1)
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMEq', insert_Ok]
  try simp only [List.head!]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hs]
  rw [show fromBool ((1 : UInt256) = 1) = (1 : UInt256) from by decide]
  refine ⟨_, rfl, ?_⟩
  exact lookup_insert_self_fin

/-- **Anything else blocks**: a status that is neither `Unreceived (0)` nor
`Verified (1)` — in particular `FullyExecuted (2)` — computes `expr_11 = 0`,
so the `require` reverts with `BundleAlreadyProcessed`. -/
theorem status_blocked
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {s : Literal}
    (hs : (Ok evm store)["expr_component_14"]!! = s)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    ∃ σ' : VarStore,
      exec (fuel+1) statusGuard (Ok evm store) = Ok evm σ'
      ∧ (Ok evm σ')["expr_11"]!! = 0 := by
  unfold statusGuard
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMIszero', insert_Ok]
  try simp only [List.head!]
  rw [hs]
  rw [show fromBool (s = 0) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hs0, if_false]]
  -- if iszero(expr_11) with expr_11 = 0 — enter
  rw [cons, nil, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  try simp only [lookup_insert_self_fin]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_pos (by decide : fromBool (decide True) ≠ (0 : UInt256))]
  -- _20 := _1
  rw [cons, Assign']
  simp only [Var', insert_Ok]
  -- expr_11 := eq(expr_component_14, 1)
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMEq', insert_Ok]
  try simp only [List.head!]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hs]
  rw [show fromBool (s = 1) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hs1, if_false]]
  refine ⟨_, rfl, ?_⟩
  exact lookup_insert_self_fin

/-! ### The composite: a delivered bundle cannot pass the guard again -/

/-- **NO DOUBLE DELIVERY (new corpus).**  After the mark's status write, the
status read back the way `fun_getBundleData` reads it — `and(sload(slot), 255)`
— is exactly `FullyExecuted = 2` (old corpus's pure readback lemma), and the
`executeBundle` status guard run on that status computes `expr_11 = 0`: the
second delivery reverts with `BundleAlreadyProcessed`.  The write lands before
any bundle call runs (CEI), so this holds even against reentrancy from the
bundle's own calls. -/
theorem no_double_delivery_guard
    {evm evm' : EVMState} {store : VarStore} {fuel : ℕ} {d : UInt256}
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome)
    (hs : (Ok evm' store)["expr_component_14"]!!
      = Fin.land
          ((evm.sstore d (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 2)).sload d)
          255) :
    ∃ σ' : VarStore,
      exec (fuel+1) statusGuard (Ok evm' store) = Ok evm' σ'
      ∧ (Ok evm' σ')["expr_11"]!! = 0 := by
  rw [generated.InteropHandler.InteropHandler.delivered_status_reads_two hacc] at hs
  exact status_blocked hs (by decide) (by decide)

/-! ### The require helper: pass on nonzero, revert with `BundleAlreadyProcessed` on zero -/

/-- The body-if of the generated
`require_helper_error_BundleAlreadyProcessed_bytes32(condition, expr)`, quoted
verbatim (selector `0x5bba5111 = 1538937105`, split let per the generator). -/
private def requireIf : Stmt := <s
  if iszero(condition)
  {
      let split_expr_0 := shl(224, 1538937105)
      mstore(0, split_expr_0)
      mstore(4, expr)
      revert(0, 36)
  }
>

/-- **PASS**: a nonzero condition falls through with the state unchanged. -/
theorem require_bap_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {c : Literal}
    (hc : (Ok evm store)["condition"]!! = c) (hc0 : c ≠ 0) :
    exec (fuel+1) requireIf (Ok evm store) = Ok evm store := by
  unfold requireIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [hc]
  rw [show fromBool (c = 0) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hc0, if_false]]
  simp only [List.head!]
  rw [if_neg (by exact fun h => h rfl)]

/-- **REVERT**: a zero condition runs the error path — selector + payload are
written and the call REVERTS. -/
theorem require_bap_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hc : (Ok evm store)["condition"]!! = 0) :
    (exec (fuel+1) requireIf (Ok evm store)).evm.reverted = true := by
  unfold requireIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [hc]
  try rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- let split_expr_0 := shl(224, 1538937105)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- mstore(0, split_expr_0)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  -- mstore(4, expr)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  -- revert(0, 36)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMRevert',
             evm_Ok, setEvm_Ok]
  rfl

/-- **NO DOUBLE DELIVERY, END TO END.**  After the CEI mark, run the status
guard on the re-read status and feed its output to the require helper (the
call boundary is the explicit `hbind` hypothesis: the callee binds `condition`
to the guard's `expr_11`, exactly what the dispatcher's
`require_helper_error_BundleAlreadyProcessed_bytes32(expr_11, …)` call does):
the helper REVERTS.  A second delivery of a delivered bundle cannot complete. -/
theorem no_double_delivery_reverts
    {evm evm' : EVMState} {store σc : VarStore} {fuel : ℕ} {d : UInt256}
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome)
    (hs : (Ok evm' store)["expr_component_14"]!!
      = Fin.land
          ((evm.sstore d (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 2)).sload d)
          255)
    (hbind : ∀ σ' : VarStore,
      exec (fuel+1) statusGuard (Ok evm' store) = Ok evm' σ' →
        (Ok evm' σc)["condition"]!! = (Ok evm' σ')["expr_11"]!!) :
    (exec (fuel+1) requireIf (Ok evm' σc)).evm.reverted = true := by
  obtain ⟨σ', hexec, hval⟩ := no_double_delivery_guard hacc hs
  refine require_bap_reverts ?_
  rw [hbind σ' hexec, hval]

end

end generated.L2InteropHandler.L2InteropHandler
