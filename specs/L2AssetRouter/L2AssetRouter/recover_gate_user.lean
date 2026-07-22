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

private lemma reviveJump_of_isOk {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

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

/-! ### Closed forms of the two calldata helpers (evm-pure calls) -/

/-- **The `[:4]` slice**: with `length ≥ 4` the bounds check passes and the
call returns `(offset, 4)`, evm untouched. -/
lemma slice4_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {O L : Literal}
    {o l : Identifier}
    (hL : ¬ ((4 : UInt256) > L)) :
    execCall (fuel+1) calldata_array_index_range_access_bytes_calldata_11718
        [o, l] (Ok evm store, [O, L])
      = Ok evm ((store.insert l 4).insert o O) := by
  unfold execCall call calldata_array_index_range_access_bytes_calldata_11718
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, cons, cons, nil]
  simp only [Assign', LetEq', LetPrimCall', AssignPrimCall', If',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMGt']
  have hok0 : isOk ((Ok evm store)☎️⟦["offset", "length"], [O, L]⟧) :=
    isOk_initcall_of_isOk trivial
  have hok1 : isOk ((Ok evm store)☎️⟦["offset", "length"], [O, L]⟧⟦"startIndex" ↦ 0⟧) := by
    rw [isOk_insert]; exact hok0
  have hok2 : isOk ((Ok evm store)☎️⟦["offset", "length"], [O, L]⟧⟦"startIndex" ↦ 0⟧⟦"startIndex" ↦ 0⟧) := by
    rw [isOk_insert]; exact hok1
  -- the bounds check reads `length`
  have hlenl : ((Ok evm store)☎️⟦["offset", "length"], [O, L]⟧⟦"startIndex" ↦ 0⟧⟦"startIndex" ↦ 0⟧)["length"]!!
      = L := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact lookup_initcall_2 (by decide)
  rw [hlenl]
  rw [show fromBool ((4 : UInt256) > L) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hL, if_false]]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- offsetOut := offset
  have hoffl : ((Ok evm store)☎️⟦["offset", "length"], [O, L]⟧⟦"startIndex" ↦ 0⟧⟦"startIndex" ↦ 0⟧)["offset"]!!
      = O := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact lookup_initcall_1
  rw [hoffl]
  -- the two ret lookups
  have hok3 : isOk ((Ok evm store)☎️⟦["offset", "length"], [O, L]⟧⟦"startIndex" ↦ 0⟧⟦"startIndex" ↦ 0⟧⟦"offsetOut" ↦ O⟧) := by
    rw [isOk_insert]; exact hok2
  have hok4 : isOk ((Ok evm store)☎️⟦["offset", "length"], [O, L]⟧⟦"startIndex" ↦ 0⟧⟦"startIndex" ↦ 0⟧⟦"offsetOut" ↦ O⟧⟦"lengthOut" ↦ 4⟧) := by
    rw [isOk_insert]; exact hok3
  have hretl : ((Ok evm store)☎️⟦["offset", "length"], [O, L]⟧⟦"startIndex" ↦ 0⟧⟦"startIndex" ↦ 0⟧⟦"offsetOut" ↦ O⟧⟦"lengthOut" ↦ 4⟧)["lengthOut"]!!
      = 4 := lookup_insert' hok3
  have hreto : ((Ok evm store)☎️⟦["offset", "length"], [O, L]⟧⟦"startIndex" ↦ 0⟧⟦"startIndex" ↦ 0⟧⟦"offsetOut" ↦ O⟧⟦"lengthOut" ↦ 4⟧)["offsetOut"]!!
      = O := by
    rw [lookup_insert_of_ne (by decide)]
    exact lookup_insert' hok2
  rw [hretl, hreto]
  obtain ⟨e4, σ4, h4⟩ := State_of_isOk hok4
  have he4 : e4 = evm := by
    have h := congrArg State.evm h4
    rw [evm_insert, evm_insert, evm_insert, evm_insert] at h
    rw [show ((Ok evm store)☎️⟦["offset", "length"], [O, L]⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at h
    exact h.symm
  rw [h4]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [insert_Ok]
  rw [he4]

/-- **The `bytes4` extraction** at `len = 4`: the call returns the first
calldata word masked to its top four bytes (the raw `calldataload` value is
kept symbolic — no byte-content claims), evm untouched. -/
lemma bytes4_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {A : Literal}
    {v : Identifier} :
    execCall (fuel+1) convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes4
        [v] (Ok evm store, [A, 4])
      = Ok evm (store.insert v
          (Fin.land (evm.calldataload A) (Fin.shiftLeft 4294967295 224))) := by
  unfold execCall call convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes4
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, cons, nil]
  simp only [Assign', LetEq', LetPrimCall', AssignPrimCall', If',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil,
             EVMCalldataload', EVMShl', EVMAnd', EVMLt']
  have hok0 : isOk ((Ok evm store)☎️⟦["array", "len"], [A, 4]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["array", "len"], [A, 4]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  -- the calldataload argument
  have harr : ((Ok evm store)☎️⟦["array", "len"], [A, 4]⟧)["array"]!! = A :=
    lookup_initcall_1
  rw [harr, hevm0]
  have hok1 : isOk ((Ok evm store)☎️⟦["array", "len"], [A, 4]⟧⟦"_1" ↦ evm.calldataload A⟧) := by
    rw [isOk_insert]; exact hok0
  have hok2 : isOk ((Ok evm store)☎️⟦["array", "len"], [A, 4]⟧⟦"_1" ↦ evm.calldataload A⟧⟦"split_expr_0" ↦ Fin.shiftLeft 4294967295 224⟧) := by
    rw [isOk_insert]; exact hok1
  -- the `and` arguments
  have h1l : ((Ok evm store)☎️⟦["array", "len"], [A, 4]⟧⟦"_1" ↦ evm.calldataload A⟧⟦"split_expr_0" ↦ Fin.shiftLeft 4294967295 224⟧)["_1"]!!
      = evm.calldataload A := by
    rw [lookup_insert_of_ne (by decide)]
    exact lookup_insert' hok0
  have h0l : ((Ok evm store)☎️⟦["array", "len"], [A, 4]⟧⟦"_1" ↦ evm.calldataload A⟧⟦"split_expr_0" ↦ Fin.shiftLeft 4294967295 224⟧)["split_expr_0"]!!
      = Fin.shiftLeft 4294967295 224 := lookup_insert' hok1
  rw [h1l, h0l]
  -- the skipped `lt(len, 4)` tail
  have hok3 : isOk ((Ok evm store)☎️⟦["array", "len"], [A, 4]⟧⟦"_1" ↦ evm.calldataload A⟧⟦"split_expr_0" ↦ Fin.shiftLeft 4294967295 224⟧⟦"value" ↦ Fin.land (evm.calldataload A) (Fin.shiftLeft 4294967295 224)⟧) := by
    rw [isOk_insert]; exact hok2
  have hlenl : ((Ok evm store)☎️⟦["array", "len"], [A, 4]⟧⟦"_1" ↦ evm.calldataload A⟧⟦"split_expr_0" ↦ Fin.shiftLeft 4294967295 224⟧⟦"value" ↦ Fin.land (evm.calldataload A) (Fin.shiftLeft 4294967295 224)⟧)["len"]!!
      = 4 := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
        lookup_insert_of_ne (by decide)]
    exact lookup_initcall_2 (by decide)
  rw [hlenl]
  rw [show fromBool ((4 : UInt256) < 4) = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- the ret lookup
  have hretv : ((Ok evm store)☎️⟦["array", "len"], [A, 4]⟧⟦"_1" ↦ evm.calldataload A⟧⟦"split_expr_0" ↦ Fin.shiftLeft 4294967295 224⟧⟦"value" ↦ Fin.land (evm.calldataload A) (Fin.shiftLeft 4294967295 224)⟧)["value"]!!
      = Fin.land (evm.calldataload A) (Fin.shiftLeft 4294967295 224) :=
    lookup_insert' hok2
  rw [hretv]
  obtain ⟨e3, σ3, h3⟩ := State_of_isOk hok3
  have he3 : e3 = evm := by
    have h := congrArg State.evm h3
    rw [evm_insert, evm_insert, evm_insert, hevm0] at h
    exact h.symm
  rw [h3]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [insert_Ok]
  rw [he3]

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

/-- Chunk 1 of the selector probe (named for the drive; identical to the
inline AST in `recoverGuard`). -/
@[reducible] private def probeChunk1 : Stmt := <s
  {
      let expr_510_offset, expr_510_length := calldata_array_index_range_access_bytes_calldata_11718(var_callData_offset, var_callData_length)
      let split_expr_0 := convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes4(expr_510_offset, expr_510_length)
      let split_expr_1 := shl(224, 4294967295)
      let split_expr_2 := and(split_expr_0, split_expr_1)
      let split_expr_3 := shl(224, 2626179025)
  }
>

/-- Chunk 2 of the selector probe. -/
@[reducible] private def probeChunk2 : Stmt := <s
  {
      let split_expr_4 := eq(split_expr_2, split_expr_3)
      expr := iszero(split_expr_4)
  }
>

/-- **Probe chunk 1 closed form**: slice the selector, extract and mask it,
load the `finalizeDeposit` selector constant. -/
private lemma probe1_lemma
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {O L : Literal}
    (hoffσ : (Ok evm σ)["var_callData_offset"]!! = O)
    (hlenσ : (Ok evm σ)["var_callData_length"]!! = L)
    (hge4 : ¬ ((4 : UInt256) > L)) :
    exec (fuel+1) probeChunk1 (Ok evm σ)
      = Ok evm ((((((σ.insert "expr_510_length" 4).insert
          "expr_510_offset" O).insert
          "split_expr_0" (Fin.land (evm.calldataload O) (Fin.shiftLeft 4294967295 224))).insert
          "split_expr_1" (Fin.shiftLeft 4294967295 224)).insert
          "split_expr_2" (Fin.land (Fin.land (evm.calldataload O) (Fin.shiftLeft 4294967295 224))
            (Fin.shiftLeft 4294967295 224))).insert
          "split_expr_3" (Fin.shiftLeft 2626179025 224)) := by
  unfold probeChunk1
  -- let expr_510_offset, expr_510_length := slice4(...)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [hoffσ, hlenσ]
  rw [slice4_call hge4]
  -- let split_expr_0 := bytes4(...)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin, lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [bytes4_call]
  -- let split_expr_1 := shl(224, 4294967295)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- let split_expr_2 := and(split_expr_0, split_expr_1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAnd',
             insert_Ok]
  rw [lookup_insert_self_fin, lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  -- let split_expr_3 := shl(224, 2626179025)
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]

/-- **Probe chunk 2 closed form**: on a selector MISMATCH the probe concludes
`expr = 1` (reject). -/
private lemma probe2_lemma
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {X S : Literal}
    (h2 : (Ok evm σ)["split_expr_2"]!! = X)
    (h3 : (Ok evm σ)["split_expr_3"]!! = S)
    (hne : X ≠ S) :
    exec (fuel+1) probeChunk2 (Ok evm σ)
      = Ok evm ((σ.insert "split_expr_4" 0).insert "expr" 1) := by
  unfold probeChunk2
  -- let split_expr_4 := eq(split_expr_2, split_expr_3)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMEq',
             insert_Ok]
  rw [h2, h3]
  rw [show fromBool (X = S) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hne, if_false]]
  -- expr := iszero(split_expr_4)
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMIszero',
             insert_Ok]
  rw [lookup_insert_self_fin]
  rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]

/-- **WRONG SELECTOR RETURNS FALSE.**  Calldata that is long enough but whose
masked first four bytes are NOT the `finalizeDeposit` selector makes the probe
conclude `expr = 1`, so the guard sets `var_recovered := 0` and `leave`s: the
function returns `false` with the evm UNTOUCHED — no decode, no NTV call, no
value movement.  Together with `recover_short_returns_false` and
`only_afm_recovers`: only the AtomicFlowManager, and only with a
`finalizeDeposit` payload, can reach the recovery value path. -/
theorem recover_wrong_selector_returns_false
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {O L : Literal}
    (hoff : (Ok evm store)["var_callData_offset"]!! = O)
    (hlen : (Ok evm store)["var_callData_length"]!! = L)
    (hge : ¬ (L < (4 : UInt256)))
    (hsel : Fin.land (Fin.land (evm.calldataload O) (Fin.shiftLeft 4294967295 224))
        (Fin.shiftLeft 4294967295 224)
      ≠ Fin.shiftLeft 2626179025 224) :
    ∃ σ' : VarStore,
      exec (fuel+1) recoverGuard (Ok evm store) = 🚪 (Ok evm σ')
      ∧ (Ok evm σ')["var_recovered"]!! = 0 := by
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
  rw [show fromBool (L < 4) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hge, if_false]]
  -- the selector probe: iszero(expr) with expr = 0 — ENTER
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  try simp only [lookup_insert_self_fin]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_pos (by decide : fromBool (decide True) ≠ (0 : UInt256))]
  -- peel the trailing false-return if into exec position, then the chunk
  rw [cons, cons]
  rw [probe1_lemma (O := O) (L := L)
    (by rw [lookup_insert_ne_fin (by decide)]; exact hoff)
    (by rw [lookup_insert_ne_fin (by decide)]; exact hlen)
    hge]
  -- chunk 2
  rw [cons]
  simp only [nil]
  rw [probe2_lemma
    (X := Fin.land (Fin.land (evm.calldataload O) (Fin.shiftLeft 4294967295 224))
      (Fin.shiftLeft 4294967295 224))
    (S := Fin.shiftLeft 2626179025 224)
    (by rw [lookup_insert_ne_fin (by decide)]; exact lookup_insert_self_fin)
    (by exact lookup_insert_self_fin)
    hsel]
  -- the false-return if (already in exec position): expr = 1 — enter
  rw [If']
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
  refine ⟨_, rfl, ?_⟩
  exact lookup_insert_self_fin


/-- **Probe chunk 2, match direction**: on a selector MATCH the probe concludes
`expr = 0` (accept). -/
private lemma probe2_match_lemma
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {X S : Literal}
    (h2 : (Ok evm σ)["split_expr_2"]!! = X)
    (h3 : (Ok evm σ)["split_expr_3"]!! = S)
    (heq : X = S) :
    exec (fuel+1) probeChunk2 (Ok evm σ)
      = Ok evm ((σ.insert "split_expr_4" 1).insert "expr" 0) := by
  unfold probeChunk2
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMEq',
             insert_Ok]
  rw [h2, h3]
  rw [show fromBool (X = S) = (1 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_true heq, if_true]]
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMIszero',
             insert_Ok]
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]

/-- **A CORRECT `finalizeDeposit` PAYLOAD CONTINUES** (liveness side): with
enough calldata and a MATCHING selector, the guard concludes `expr = 0` and
falls through — no false return, no revert; execution proceeds to the decode
and the NTV recovery forward.  The gate blocks exactly the wrong payloads. -/
theorem recover_selector_match_continues
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {O L : Literal}
    (hoff : (Ok evm store)["var_callData_offset"]!! = O)
    (hlen : (Ok evm store)["var_callData_length"]!! = L)
    (hge : ¬ (L < (4 : UInt256)))
    (hsel : Fin.land (Fin.land (evm.calldataload O) (Fin.shiftLeft 4294967295 224))
        (Fin.shiftLeft 4294967295 224)
      = Fin.shiftLeft 2626179025 224) :
    ∃ σ' : VarStore,
      exec (fuel+1) recoverGuard (Ok evm store) = Ok evm σ' := by
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
  rw [show fromBool (L < 4) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hge, if_false]]
  -- the selector probe: iszero(expr) with expr = 0 — ENTER
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  try simp only [lookup_insert_self_fin]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_pos (by decide : fromBool (decide True) ≠ (0 : UInt256))]
  -- peel the trailing false-return if into exec position, then the chunk
  rw [cons, cons]
  rw [probe1_lemma (O := O) (L := L)
    (by rw [lookup_insert_ne_fin (by decide)]; exact hoff)
    (by rw [lookup_insert_ne_fin (by decide)]; exact hlen)
    hge]
  -- chunk 2, match direction
  rw [cons]
  simp only [nil]
  rw [probe2_match_lemma
    (X := Fin.land (Fin.land (evm.calldataload O) (Fin.shiftLeft 4294967295 224))
      (Fin.shiftLeft 4294967295 224))
    (S := Fin.shiftLeft 2626179025 224)
    (by rw [lookup_insert_ne_fin (by decide)]; exact lookup_insert_self_fin)
    (by exact lookup_insert_self_fin)
    hsel]
  -- the false-return if (in exec position): expr = 0 — SKIP
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append]
  try simp only [lookup_insert_self_fin]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  exact ⟨_, rfl⟩

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
