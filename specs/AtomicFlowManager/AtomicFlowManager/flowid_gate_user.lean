import Clear.ReasoningPrinciple

import specs.AtomicFlowManager.AtomicFlowManager.inclusion_gate_user
import generated.AtomicFlowManager.AtomicFlowManager.fun_checkFlowId
import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_uint256_dyn_calldata

/-
  THE FLOW-ID GATE'S GUARDS — the flow structure is canonical and bound.

  `_checkFlowId` (called by BOTH `requireFlowFinalized` and `authorizeRefund`
  before any proof is checked) recomputes
  `flowId = keccak256(abi.encode(legBundleHashes, legSourceChainIds,
  deadline, settlementLayerChainId))` and guards:

  * the leg bundle hashes are STRICTLY ASCENDING (canonical order — no
    duplicate legs, no permuted re-presentations of the same flow),
  * `legSourceChainIds` is aligned 1:1 with the bundle hashes,
  * the declared `flowId` EQUALS the recomputed hash.

  This file proves the guards over their verbatim compiled blocks: the
  sortedness comparison and the flowId comparison in BOTH directions, the
  length comparison in the pass direction.  Since the commit value bakes the
  `flowId` in (#33), acceptance by either gate means the deadline and leg set
  the gate then uses are EXACTLY the ones every leg's tree commitment binds —
  no swapped deadline, no injected leg, no reordered flow.

  Axiom-free.
-/

namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-! ### Local state-plumbing helpers -/

@[simp] private lemma insert_Ok {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

private lemma evm_Ok {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

private lemma setEvm_Ok {e E : EVMState} {σ : VarStore} :
    (Ok e σ).setEvm E = Ok E σ := rfl

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

/-! ### The three guard blocks, quoted verbatim from the body -/

/-- The sortedness guard (loop body tail): revert unless
`legBundleHashes[i] > legBundleHashes[i-1]`. -/
private def sortGuard : Stmt := <s
  {
    let split_expr_1 := gt(value, value_1)
    if iszero(split_expr_1)
    {
        let split_expr_2 := shl(225, 2012753307)
        mstore(0, split_expr_2)
        revert(0, 4)
    }
}
>

/-- The length guard: revert unless `legSourceChainIds.length =
legBundleHashes.length`. -/
private def lenGuard : Stmt := <s
  {
    let split_expr_3 := eq(expr_607_length, expr_576_length)
    if iszero(split_expr_3)
    {
        let expr_614_offset, expr_614_length := access_calldata_tail_array_uint256_dyn_calldata(var_flow_offset, _4)
        let split_expr_4 := shl(224, 3785850835)
        mstore(0, split_expr_4)
        let split_expr_5 := abi_encode_uint256_uint256_7396(expr_576_length, expr_614_length)
        revert(0, split_expr_5)
    }
}
>

/-- The flowId guard: revert unless the recomputed hash equals the declared
`flowId`. -/
private def flowGuard : Stmt := <s
  {
    let split_expr_12 := eq(expr_1, value_3)
    if iszero(split_expr_12)
    {
        let split_expr_13 := shl(224, 4166537495)
        mstore(0, split_expr_13)
        let split_expr_14 := abi_encode_uint256_uint256_7396(value_3, expr_1)
        revert(0, split_expr_14)
    }
}
>

/-! ### Guard 1 — the leg bundle hashes are strictly ascending -/

/-- **PASS**: `prev < cur` — the pair is in canonical order. -/
theorem sorted_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {cur prev : Literal}
    (hv : (Ok evm store)["value"]!! = cur)
    (hv1 : (Ok evm store)["value_1"]!! = prev)
    (hlt : prev < cur) :
    exec (fuel+1) sortGuard (Ok evm store)
      = Ok evm (store.insert "split_expr_1" 1) := by
  unfold sortGuard
  simp only [cons, nil]
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMGt']
  rw [hv, hv1]
  rw [show fromBool (cur > prev) = (1 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_true hlt, if_true]]
  simp only [insert_Ok]
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  simp only [List.head!]
  rw [if_neg (by exact fun h => h rfl)]

/-- **REVERT**: `cur ≤ prev` — a duplicate or out-of-order leg; the flow
presentation is not canonical. -/
theorem sorted_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {cur prev : Literal}
    (hv : (Ok evm store)["value"]!! = cur)
    (hv1 : (Ok evm store)["value_1"]!! = prev)
    (hle : ¬ (prev < cur)) :
    (exec (fuel+1) sortGuard (Ok evm store)).evm.reverted = true := by
  unfold sortGuard
  simp only [cons, nil]
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMGt']
  rw [hv, hv1]
  rw [show fromBool (cur > prev) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hle, if_false]]
  simp only [insert_Ok]
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  simp only [List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- body: shl let
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- body: mstore(0, split_expr_2)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  -- body: revert(0, 4)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMRevert',
             evm_Ok, setEvm_Ok]
  rfl

/-! ### Guard 2 — the leg source-chain array is aligned (pass direction) -/

/-- **PASS**: the two leg arrays have EQUAL length — the source-chain
binding is positional and total. -/
theorem length_match_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {n m : Literal}
    (hn : (Ok evm store)["expr_607_length"]!! = m)
    (hm : (Ok evm store)["expr_576_length"]!! = n)
    (heq : m = n) :
    exec (fuel+1) lenGuard (Ok evm store)
      = Ok evm (store.insert "split_expr_3" 1) := by
  unfold lenGuard
  simp only [cons, nil]
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMEq']
  rw [hn, hm]
  rw [show fromBool (m = n) = (1 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_true heq, if_true]]
  simp only [insert_Ok]
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  simp only [List.head!]
  rw [if_neg (by exact fun h => h rfl)]

/-! ### Guard 3 — the declared flowId IS the recomputed hash -/

/-- **PASS**: the recomputed `keccak(abi.encode(...))` equals the declared
`flowId`; the pair records the (true) comparison and falls through. -/
theorem flowid_match_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {computed declared : Literal}
    (hc : (Ok evm store)["expr_1"]!! = computed)
    (hd : (Ok evm store)["value_3"]!! = declared)
    (heq : computed = declared) :
    exec (fuel+1) flowGuard (Ok evm store)
      = Ok evm (store.insert "split_expr_12" 1) := by
  unfold flowGuard
  simp only [cons, nil]
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMEq']
  rw [hc, hd]
  rw [show fromBool (computed = declared) = (1 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_true heq, if_true]]
  simp only [insert_Ok]
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  simp only [List.head!]
  rw [if_neg (by exact fun h => h rfl)]

/-- **REVERT**: the declared `flowId` does NOT match the flow's contents —
a tampered deadline, leg set, or settlement layer is rejected before any
proof is examined. -/
theorem flowid_mismatch_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {computed declared : Literal}
    (hc : (Ok evm store)["expr_1"]!! = computed)
    (hd : (Ok evm store)["value_3"]!! = declared)
    (hne : computed ≠ declared) :
    (exec (fuel+1) flowGuard (Ok evm store)).evm.reverted = true := by
  unfold flowGuard
  simp only [cons, nil]
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMEq']
  rw [hc, hd]
  rw [show fromBool (computed = declared) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hne, if_false]]
  simp only [insert_Ok]
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  simp only [List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- body: shl let
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- body: mstore(0, split_expr_13)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  -- body: split_expr_14 := abi_encode_uint256_uint256_7396(...)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [abi7396_call]
  -- body: revert(0, split_expr_14)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMRevert',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rfl

end

end generated.AtomicFlowManager.AtomicFlowManager
