import Clear.ReasoningPrinciple

import specs.AtomicFlowManager.AtomicFlowManager.inclusion_gate_user
import generated.AtomicFlowManager.AtomicFlowManager.fun_verifyTimeoutAdjacency

/-
  THE TIMEOUT GATE'S TEMPORAL GUARDS — acceptance pins #34's premises.

  `verifyTimeoutAdjacency` (the reclaim gate's outer verifier) guards the
  adjacency-timeout semantics with three comparisons:

  * the ABSENCE batch is on time            (`if gt(tN, deadline) revert`),
  * the SUCCESSOR batch is past the deadline (`if iszero(gt(tS, deadline)) revert`),
  * the two batches are CONSECUTIVE          (`if iszero(eq(bS, bN+1)) revert`).

  This file proves each guard in BOTH directions over its exact statement
  block (quoted verbatim from the compiled body): the guard falls through
  iff its temporal condition holds, and reverts otherwise.  So any accepting
  run of the gate satisfies `tN ≤ D ∧ D < tS ∧ bS = bN + 1` — precisely the
  successor-pinning premises of the abstract never-both theorem (#34,
  `delivered_and_reclaimed_impossible`, with `t i ≤ D` on the delivery side
  guarded symmetrically by `verifyInclusion`'s deadline check).

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

private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok]; exact lookup_insert_of_ne h

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

private lemma evm_setEvm_of_isOk {s : State} {e : EVMState} (h : isOk s) :
    (s.setEvm e).evm = e := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma reviveJump_of_isOk {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma lookup_setEvm_of_isOk {s : State} {e : EVMState} {k : Identifier}
    (h : isOk s) : (s.setEvm e)[k]!! = s[k]!! := by
  obtain ⟨evm₀, st, rfl⟩ := State_of_isOk h; rfl

/-! ### `abi_encode_uint256_uint64` closed form (the temporal reverts' encoder) -/

lemma abi64_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {v0 v1 : Literal} {t : Identifier} :
    execCall (fuel+1) abi_encode_uint256_uint64 [t] (Ok evm store, [v0, v1])
      = Ok ((evm.mstore 4 v0).mstore 36 (Fin.land v1 18446744073709551615))
          (store.insert t 68) := by
  unfold execCall call abi_encode_uint256_uint64
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, cons, nil]
  simp only [Assign', LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMstore', EVMAnd']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hok1 : isOk ((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧⟦"tail" ↦ 68⟧) := by
    rw [isOk_insert]; exact hok0
  -- first mstore argument
  have hv0l : ((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧⟦"tail" ↦ 68⟧)["value0"]!!
      = v0 := by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_initcall_1
  rw [hv0l]
  simp only [evm_insert]
  rw [hevm0]
  -- the `and` argument
  have hok2 : isOk (((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧⟦"tail" ↦ 68⟧).setEvm
      (evm.mstore 4 v0)) := by
    rw [isOk_setEvm]; exact hok1
  have hv1l : (((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧⟦"tail" ↦ 68⟧).setEvm
      (evm.mstore 4 v0))["value1"]!! = v1 := by
    rw [lookup_setEvm_of_isOk hok1, lookup_insert_of_ne (by decide)]
    exact lookup_initcall_2 (by decide)
  rw [hv1l]
  -- the second mstore: split_expr_0 lookup, evm resolution
  have hok3 : isOk ((((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧⟦"tail" ↦ 68⟧).setEvm
      (evm.mstore 4 v0))⟦"split_expr_0" ↦ Fin.land v1 18446744073709551615⟧) := by
    rw [isOk_insert]; exact hok2
  have hsel : ((((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧⟦"tail" ↦ 68⟧).setEvm
      (evm.mstore 4 v0))⟦"split_expr_0" ↦ Fin.land v1 18446744073709551615⟧)["split_expr_0"]!!
      = Fin.land v1 18446744073709551615 := lookup_insert' hok2
  rw [hsel]
  rw [evm_setEvm_of_isOk hok1]
  -- the `tail` return lookup on the final state
  have hok4 : isOk (((((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧⟦"tail" ↦ 68⟧).setEvm
      (evm.mstore 4 v0))⟦"split_expr_0" ↦ Fin.land v1 18446744073709551615⟧).setEvm
      ((evm.mstore 4 v0).mstore 36 (Fin.land v1 18446744073709551615))) := by
    rw [isOk_setEvm]; exact hok3
  have htail : (((((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧⟦"tail" ↦ 68⟧).setEvm
      (evm.mstore 4 v0))⟦"split_expr_0" ↦ Fin.land v1 18446744073709551615⟧).setEvm
      ((evm.mstore 4 v0).mstore 36 (Fin.land v1 18446744073709551615)))["tail"]!! = 68 := by
    rw [lookup_setEvm_of_isOk hok3, lookup_insert_of_ne (by decide),
        lookup_setEvm_of_isOk hok1]
    exact lookup_insert' hok0
  rw [htail]
  obtain ⟨e4, σ4, h4⟩ := State_of_isOk hok4
  have he4 : e4 = (evm.mstore 4 v0).mstore 36 (Fin.land v1 18446744073709551615) := by
    have h := congrArg State.evm h4
    rw [evm_setEvm_of_isOk hok3] at h
    exact h.symm
  rw [h4]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [insert_Ok]
  rw [he4]

/-! ### The three temporal guard blocks, quoted verbatim from the body -/

/-- The absence-deadline guard: revert if batch `N` settled past the deadline. -/
private def absGuard : Stmt := <s
  if gt(expr_1173_component_1, _1)
{
    let split_expr_3 := shl(227, 86127855)
    mstore(0, split_expr_3)
    let split_expr_4 := abi_encode_uint256_uint64(expr_1173_component_1, var__deadline)
    revert(0, split_expr_4)
}
>

/-- The successor-deadline guard: compute `gt(tS, deadline)`, revert if the
successor is still in time. -/
private def sucGuard : Stmt := <s
  {
    let split_expr_28 := gt(expr_1225_component_2, _1)
    if iszero(split_expr_28)
    {
        let split_expr_29 := shl(224, 4273435075)
        mstore(0, split_expr_29)
        let split_expr_30 := abi_encode_uint256_uint64(expr_1225_component_2, var__deadline)
        revert(0, split_expr_30)
    }
}
>

/-- The adjacency guard: compute `eq(bS, bN+1)`, revert if not consecutive. -/
private def adjGuard : Stmt := <s
  {
    let split_expr_25 := eq(value_4, split_expr_24)
    if iszero(split_expr_25)
    {
        let split_expr_26 := shl(224, 824723171)
        mstore(0, split_expr_26)
        let split_expr_27 := abi_encode_uint256_uint256_7396(value_5, value_4)
        revert(0, split_expr_27)
    }
}
>

/-! ### Guard 1 — the absence batch is on time -/

/-- **PASS**: `tN ≤ D̂` — the guard falls through with the state unchanged. -/
theorem absence_ontime_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {tN D : Literal}
    (htN : (Ok evm store)["expr_1173_component_1"]!! = tN)
    (hD : (Ok evm store)["_1"]!! = D)
    (hle : ¬ (D < tN)) :
    exec (fuel+1) absGuard (Ok evm store) = Ok evm store := by
  unfold absGuard
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMGt']
  rw [htN, hD]
  rw [show fromBool (tN > D) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hle, if_false]]
  simp only [List.head!]
  rw [if_neg (by exact fun h => h rfl)]

/-- **REVERT**: `D̂ < tN` — the absence batch is late, the guard reverts. -/
theorem absence_late_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {tN D : Literal}
    (htN : (Ok evm store)["expr_1173_component_1"]!! = tN)
    (hD : (Ok evm store)["_1"]!! = D)
    (hlt : D < tN) :
    (exec (fuel+1) absGuard (Ok evm store)).evm.reverted = true := by
  unfold absGuard
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMGt']
  rw [htN, hD]
  rw [show fromBool (tN > D) = (1 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_true hlt, if_true]]
  simp only [List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- body: shl let
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- body: mstore(0, split_expr_3)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  -- body: split_expr_4 := abi_encode_uint256_uint64(...)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [abi64_call]
  -- body: revert(0, split_expr_4)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMRevert',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rfl

/-! ### Guard 2 — the successor batch is past the deadline -/

/-- **PASS**: `D̂ < tS` — the successor pins the deadline; the pair records
the (true) comparison and falls through. -/
theorem successor_late_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {tS D : Literal}
    (htS : (Ok evm store)["expr_1225_component_2"]!! = tS)
    (hD : (Ok evm store)["_1"]!! = D)
    (hlt : D < tS) :
    exec (fuel+1) sucGuard (Ok evm store)
      = Ok evm (store.insert "split_expr_28" 1) := by
  unfold sucGuard
  simp only [cons, nil]
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMGt']
  rw [htS, hD]
  rw [show fromBool (tS > D) = (1 : UInt256) from by
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

/-- **REVERT**: `tS ≤ D̂` — the successor is still in time (batch `N` is not
pinned as the last on-time one), the guard reverts. -/
theorem successor_ontime_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {tS D : Literal}
    (htS : (Ok evm store)["expr_1225_component_2"]!! = tS)
    (hD : (Ok evm store)["_1"]!! = D)
    (hle : ¬ (D < tS)) :
    (exec (fuel+1) sucGuard (Ok evm store)).evm.reverted = true := by
  unfold sucGuard
  simp only [cons, nil]
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMGt']
  rw [htS, hD]
  rw [show fromBool (tS > D) = (0 : UInt256) from by
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
  -- body: mstore(0, split_expr_29)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  -- body: split_expr_30 := abi_encode_uint256_uint64(...)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [abi64_call]
  -- body: revert(0, split_expr_30)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMRevert',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rfl

/-! ### Guard 3 — the batches are consecutive -/

/-- **PASS**: `bS = bN + 1` — the batches are consecutive; the pair records
the (true) comparison and falls through. -/
theorem adjacency_consecutive_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {bS bN1 : Literal}
    (h4 : (Ok evm store)["value_4"]!! = bS)
    (h24 : (Ok evm store)["split_expr_24"]!! = bN1)
    (heq : bS = bN1) :
    exec (fuel+1) adjGuard (Ok evm store)
      = Ok evm (store.insert "split_expr_25" 1) := by
  unfold adjGuard
  simp only [cons, nil]
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMEq']
  rw [h4, h24]
  rw [show fromBool (bS = bN1) = (1 : UInt256) from by
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

/-- **REVERT**: `bS ≠ bN + 1` — the batches are not consecutive, the guard
reverts. -/
theorem adjacency_gap_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {bS bN1 : Literal}
    (h4 : (Ok evm store)["value_4"]!! = bS)
    (h24 : (Ok evm store)["split_expr_24"]!! = bN1)
    (hne : bS ≠ bN1) :
    (exec (fuel+1) adjGuard (Ok evm store)).evm.reverted = true := by
  unfold adjGuard
  simp only [cons, nil]
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMEq']
  rw [h4, h24]
  rw [show fromBool (bS = bN1) = (0 : UInt256) from by
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
  -- body: mstore(0, split_expr_26)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  -- body: split_expr_27 := abi_encode_uint256_uint256_7396(...)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [abi7396_call]
  -- body: revert(0, split_expr_27)
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
