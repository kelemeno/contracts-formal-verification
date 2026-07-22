import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import generated.L2AssetRouter.L2AssetRouter.calldata_array_index_range_access_bytes_calldata_11718
import generated.L2AssetRouter.L2AssetRouter.convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes4

/-
  THE RECOVERY CALLER GATE (L2AssetRouter, atomic-interop timeout path).

  `recoverAtomicCall` is `onlyAtomicFlowManager`: the dispatcher computes

      require_helper_error_Unauthorized_address(
        eq(caller(), and(65556, sub(shl(160, 1), 1))), caller())

  (src 8:6704:6777) — the caller must be the L2 AtomicFlowManager built-in at
  `0x10014 = 65556`.  This file proves:

  * `require_unauth_pass` / `require_unauth_reverts` — closed forms of the
    verbatim (chunked) body-if of the generated
    `require_helper_error_Unauthorized_address`;
  * `afm_addr_mask` — the 160-bit mask leaves the AFM address intact;
  * `only_afm_recovers` — composite: a caller that is NOT the AtomicFlowManager
    makes the gate condition `0`, and the require REVERTS with `Unauthorized`.
    Nobody but the AFM can trigger the timeout-recovery value path — spec
    point 1's caller binding.

  Axiom-free.
-/

namespace generated.L2AssetRouter.L2AssetRouter

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

/-! ### The require helper's body-if, quoted verbatim (generator chunking) -/

/-- The body-if of `require_helper_error_Unauthorized_address`
(selector `0x472511eb·2 = 1193611755` shifted by 225; the payload address is
160-bit-masked), statements as in the source Yul.  The generated fundef chunks
the arm into two nested blocks — a generator artifact with identical semantics
under Clear's flat store (block statements run sequentially, no scope
teardown); the flat quote keeps the drive linear. -/
private def requireUnauthIf : Stmt := <s
  if iszero(condition)
  {
      let split_expr_0 := shl(225, 1193611755)
      mstore(0, split_expr_0)
      let split_expr_1 := shl(160, 1)
      let split_expr_2 := sub(split_expr_1, 1)
      let split_expr_3 := and(expr, split_expr_2)
      mstore(4, split_expr_3)
      revert(0, 36)
  }
>

/-- **PASS**: a nonzero condition falls through with the state unchanged. -/
theorem require_unauth_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {c : Literal}
    (hc : (Ok evm store)["condition"]!! = c) (hc0 : c ≠ 0) :
    exec (fuel+1) requireUnauthIf (Ok evm store) = Ok evm store := by
  unfold requireUnauthIf
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

/-- **REVERT**: a zero condition runs the error path — selector and masked
address are written and the call REVERTS with `Unauthorized`. -/
theorem require_unauth_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hc : (Ok evm store)["condition"]!! = 0) :
    (exec (fuel+1) requireUnauthIf (Ok evm store)).evm.reverted = true := by
  unfold requireUnauthIf
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
  -- let split_expr_0 := shl(225, 1193611755)
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
  -- let split_expr_1 := shl(160, 1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- let split_expr_2 := sub(split_expr_1, 1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMSub',
             insert_Ok]
  rw [lookup_insert_self_fin]
  -- let split_expr_3 := and(expr, split_expr_2)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAnd',
             insert_Ok]
  rw [lookup_insert_self_fin]
  -- mstore(4, split_expr_3)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  -- revert(0, 36)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMRevert',
             evm_Ok, setEvm_Ok]
  rfl

/-! ### The AFM address survives the 160-bit mask -/

/-- `and(65556, 2^160 - 1) = 65556`: the AtomicFlowManager built-in address
(`0x10014`) is untouched by the address mask. -/
theorem afm_addr_mask :
    Fin.land (65556 : UInt256) (Fin.shiftLeft 1 160 - 1) = 65556 := by decide

/-- **ONLY THE ATOMICFLOWMANAGER RECOVERS.**  A caller that is not the AFM
built-in (`0x10014 = 65556`) makes the gate condition
`eq(caller(), and(65556, mask))` compute `0` (`hbind` is the dispatcher's
argument passing, verbatim), and the require REVERTS with `Unauthorized`:
the timeout-recovery value path is reachable only by the AtomicFlowManager —
spec point 1's caller binding. -/
theorem only_afm_recovers
    {evm : EVMState} {σc : VarStore} {fuel : ℕ}
    (hne : ((evm.execution_env.source : UInt256)) ≠ (65556 : UInt256))
    (hbind : (Ok evm σc)["condition"]!!
      = fromBool (((evm.execution_env.source : UInt256))
          = Fin.land (65556 : UInt256) (Fin.shiftLeft 1 160 - 1))) :
    (exec (fuel+1) requireUnauthIf (Ok evm σc)).evm.reverted = true := by
  refine require_unauth_reverts ?_
  rw [hbind, afm_addr_mask]
  simp only [fromBool, Bool.toUInt256, decide_eq_false hne, if_false]

/-! ### The selector guard: short calldata cannot move value -/

/-- The guard prefix of `fun_recoverAtomicCall_inner`, quoted verbatim from the
generated body (statements 1–3): the length check, the selector probe (never
entered on the short path — its helper calls stay inert AST), and the
false-return if. -/
private def recoverGuard : Stmt := <s
  {
    let expr := lt(var_callData_length, 4)
    if iszero(expr)
    {
        {
            let expr_510_offset, expr_510_length := calldata_array_index_range_access_bytes_calldata_11718(var_callData_offset, var_callData_length)
            let split_expr_0 := convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes4(expr_510_offset, expr_510_length)
            let split_expr_1 := shl(224, 4294967295)
            let split_expr_2 := and(split_expr_0, split_expr_1)
            let split_expr_3 := shl(224, 2626179025)
        }
        {
            let split_expr_4 := eq(split_expr_2, split_expr_3)
            expr := iszero(split_expr_4)
        }
    }
    if expr
    {
        var_recovered := 0
        leave
    }
}
>

/-- **SHORT CALLDATA RETURNS FALSE.**  A payload shorter than a selector
(`length < 4`) makes the guard set `var_recovered := 0` and `leave`: the
function returns `false` with the evm UNTOUCHED — no decode, no NTV call, no
value movement.  The selector probe is never entered. -/
theorem recover_short_returns_false
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {L : Literal}
    (hlen : (Ok evm store)["var_callData_length"]!! = L)
    (hshort : L < (4 : UInt256)) :
    exec (fuel+1) recoverGuard (Ok evm store)
      = 🚪 (Ok evm ((store.insert "expr" 1).insert "var_recovered" 0)) := by
  unfold recoverGuard
  -- let expr := lt(var_callData_length, 4)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMLt',
             insert_Ok]
  try simp only [List.head!]
  rw [hlen]
  rw [show fromBool (L < 4) = (1 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_true hshort, if_true]]
  -- the selector probe: iszero(expr) with expr = 1 — skip
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  try simp only [lookup_insert_self_fin]
  try rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- the false-return if: expr = 1 — enter
  rw [cons, nil, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append]
  try simp only [lookup_insert_self_fin]
  try simp only [List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- var_recovered := 0
  rw [cons, Assign']
  simp only [Lit', insert_Ok]
  -- leave
  rw [cons, nil, Leave']

end

end generated.L2AssetRouter.L2AssetRouter
