import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import generated.L2InteropHandler.L2InteropHandler.fun_executeCalls
import generated.L2InteropHandler.L2InteropHandler.memory_array_index_access_enum_CallStatus_dyn
import specs.L2InteropHandler.L2InteropHandler.mem_helpers_user

/-
  THE PER-CALL VERSION GATE (L2InteropHandler, `fun_executeCalls`).

  Every call in a delivered bundle passes through the loop-body guard
  (src 43:14493:14536): the call's version byte — the TOP byte of its first
  struct word — must equal `INTEROP_CALL_VERSION = 1`, else the whole
  delivery REVERTS (`UnsupportedInteropCallVersion`, selector
  `0xd5f13973 = 3589355891`).  No call of an unknown format is ever
  dispatched:

      if iszero(eq(and(mload(_mpos), shl(248, 255)), shl(248, 1)))
      {
          mstore(0, shl(224, 3589355891))
          revert(0, 4)
      }

  * `call_version_pass`    — a version-1 call falls through;
  * `call_version_reverts` — any other version byte reverts.

  The struct word stays SYMBOLIC (`evm.mload` term).  Axiom-free.
-/

namespace generated.L2InteropHandler.L2InteropHandler

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

private lemma lookup_ok_evm {σ : VarStore} {k : Identifier} (e e' : EVMState) :
    (Ok e σ)[k]!! = (Ok e' σ)[k]!! := rfl

/-! ### The version gate, quoted verbatim -/

/-- The per-call version guard of `fun_executeCalls`' loop body. -/
@[reducible] private def versionIf : Stmt := <s
  if iszero(eq(and(mload(_mpos), shl(248, 255)), shl(248, 1)))
  {
      mstore(0, shl(224, 3589355891))
      revert(0, 4)
  }
>

/-- **A VERSION-1 CALL PASSES**: when the call's masked version byte equals
`INTEROP_CALL_VERSION`, the guard falls through with the state unchanged. -/
theorem call_version_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {Mp : Literal}
    (hm : (Ok evm store)["_mpos"]!! = Mp)
    (hver : Fin.land (evm.mload Mp) (Fin.shiftLeft 255 248)
      = Fin.shiftLeft 1 248) :
    exec (fuel+1) versionIf (Ok evm store) = Ok evm store := by
  unfold versionIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMEq', EVMAnd', EVMShl', EVMMload', evm_Ok]
  try simp only [List.head!]
  rw [hm]
  simp only [decide_eq_true hver]
  simp only [show fromBool true = (1 : UInt256) from by decide]
  simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  simp only [show fromBool false = (0 : UInt256) from by decide]
  rw [if_neg (by exact fun h => h rfl)]

/-- **ANY OTHER VERSION REVERTS**: a call whose masked version byte is NOT
`INTEROP_CALL_VERSION` aborts the whole delivery with
`UnsupportedInteropCallVersion` — no unknown-format call is dispatched. -/
theorem call_version_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {Mp : Literal}
    (hm : (Ok evm store)["_mpos"]!! = Mp)
    (hver : Fin.land (evm.mload Mp) (Fin.shiftLeft 255 248)
      ≠ Fin.shiftLeft 1 248) :
    (exec (fuel+1) versionIf (Ok evm store)).evm.reverted = true := by
  unfold versionIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMEq', EVMAnd', EVMShl', EVMMload', evm_Ok]
  try simp only [List.head!]
  rw [hm]
  simp only [decide_eq_false hver]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  rw [if_pos (by decide : fromBool (decide True) ≠ (0 : UInt256))]
  -- mstore(0, shl(224, 3589355891))
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMShl', EVMMstore', evm_Ok, setEvm_Ok]
  try simp only [List.head!]
  -- revert(0, 4)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMRevert', evm_Ok, setEvm_Ok]
  rfl

/-! ### The value-carrier pin: funds come only from the base-token holder -/

/-- `and(65553, 2^160 - 1) = 65553`: the L2 base-token holder built-in
(`0x10011`) is untouched by the address mask — the `give` call that funds a
value-carrying interop call is pinned to it. -/
theorem bth_addr_mask :
    Fin.land (65553 : UInt256) (Fin.shiftLeft 1 160 - 1) = 65553 := by decide

/-- The code-presence guard on the value route, quoted verbatim: the pinned
holder must have code, else the delivery reverts before any value moves. -/
@[reducible] private def holderCodeIf : Stmt := <s
  if iszero(extcodesize(_5))
  {
      revert(0, 0)
  }
>

/-- **A DEPLOYED HOLDER PASSES**: nonzero code size at the pinned holder falls
through unchanged. -/
theorem holder_code_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {A : Literal}
    (hA : (Ok evm store)["_5"]!! = A)
    (hcode : evm.extCodeSize A ≠ 0) :
    exec (fuel+1) holderCodeIf (Ok evm store) = Ok evm store := by
  unfold holderCodeIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero', EVMExtcodesize', evm_Ok]
  try simp only [List.head!]
  rw [hA]
  simp only [decide_eq_false hcode]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  rw [if_neg (by exact fun h => h rfl)]

/-- **A CODELESS HOLDER REVERTS**: if the pinned holder has no code, the
delivery reverts — value cannot be sourced from a missing contract. -/
theorem holder_code_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {A : Literal}
    (hA : (Ok evm store)["_5"]!! = A)
    (hcode : evm.extCodeSize A = 0) :
    (exec (fuel+1) holderCodeIf (Ok evm store)).evm.reverted = true := by
  unfold holderCodeIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero', EVMExtcodesize', evm_Ok]
  try simp only [List.head!]
  rw [hA]
  simp only [decide_eq_true hcode]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMRevert', evm_Ok, setEvm_Ok]
  rfl

/-! ### The generic external-call failure-forward arm -/

/-- The revert-forward arm after an external call, generic over the condition
variable `k` and the scratch pointer name `pv` (constructor-built AST; the
verbatim instances below check against it by `rfl`). -/
@[reducible] private def failForwardIf (k pv : Identifier) : Stmt :=
  .If (.PrimCall .Iszero [.Var k])
    [.LetPrimCall [pv] .Mload [.Lit 64],
     .ExprStmtPrimCall .Returndatacopy [.Var pv, .Lit 0, .PrimCall .Returndatasize []],
     .ExprStmtPrimCall .Revert [.Var pv, .PrimCall .Returndatasize []]]

/-- The `give`-call failure arm of the value route, quoted verbatim. -/
@[reducible] private def giveFailIf : Stmt := <s
  if iszero(_7)
  {
      let pos := mload(64)
      returndatacopy(pos, 0, returndatasize())
      revert(pos, returndatasize())
  }
>

/-- The verbatim quote IS the generic shape. -/
example : giveFailIf = failForwardIf "_7" "pos" := rfl

/-- **A FAILED EXTERNAL CALL FORWARDS ITS REVERT** — generic: whatever the
condition and pointer names, a zero call-result runs the forward arm and ends
reverted on both `returndatacopy` branches. -/
theorem fail_forward_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {k pv : Identifier}
    (h : (Ok evm store)[k]!! = 0) :
    (exec (fuel+1) (failForwardIf k pv) (Ok evm store)).evm.reverted = true := by
  unfold failForwardIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [h]
  try rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- let pv := mload(64)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMMload', evm_Ok, insert_Ok]
  try simp only [List.head!]
  -- returndatacopy(pv, 0, returndatasize())
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil,
             EVMReturndatasize', EVMReturndatacopy', evm_Ok, insert_Ok]
  try simp only [List.head!]
  rw [lookup_insert_self_fin]
  rcases hrc : evm.returndatacopy (evm.mload 64) 0 evm.returndatasize with _ | evm'
  all_goals {
    simp only [hrc]
    simp only [setEvm_Ok]
    -- revert(pv, returndatasize())
    rw [cons, nil, ExprStmtPrimCall']
    simp only [evalArgs, evalTail, cons', head', reverse', multifill',
               PrimCall', Lit', Var', execPrimCall, evalPrimCall,
               List.reverse_cons, List.reverse_nil, List.nil_append,
               List.singleton_append, multifill_cons, multifill_nil,
               EVMReturndatasize', EVMRevert', evm_Ok, setEvm_Ok, insert_Ok]
    try simp only [List.head!]
    try rw [lookup_insert_self_fin]
    rfl
  }

/-- **A FAILED `give` CALL REVERTS THE DELIVERY**: if the pinned base-token
holder's `give` call fails, the whole delivery reverts, forwarding the
holder's revert data — value-carrying calls cannot proceed unfunded. -/
theorem give_call_failure_forwards
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (h7 : (Ok evm store)["_7"]!! = 0) :
    (exec (fuel+1) giveFailIf (Ok evm store)).evm.reverted = true :=
  fail_forward_reverts h7

/-- The `receiveMessage`-dispatch failure arm, quoted verbatim. -/
@[reducible] private def dispatchFailIf : Stmt := <s
  if iszero(_11)
  {
      let pos_1 := mload(64)
      returndatacopy(pos_1, 0, returndatasize())
      revert(pos_1, returndatasize())
  }
>

/-- The verbatim quote IS the generic shape. -/
example : dispatchFailIf = failForwardIf "_11" "pos_1" := rfl

/-- **BUNDLE ATOMICITY (per-call leg)**: if ANY call's `receiveMessage`
dispatch fails, the whole delivery reverts, forwarding the recipient's revert
data — a bundle executes all of its calls or none of them. -/
theorem dispatch_call_failure_forwards
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (h11 : (Ok evm store)["_11"]!! = 0) :
    (exec (fuel+1) dispatchFailIf (Ok evm store)).evm.reverted = true :=
  fail_forward_reverts h11

/-! ### The empty bundle: a full closed form of `fun_executeCalls` -/

/-- **AN EMPTY BUNDLE DISPATCHES NOTHING** — the first full-function closed
form in this corpus: with `calls.length = 0` the loop condition fails at
entry, and `fun_executeCalls` returns with the caller's store and the evm
UNTOUCHED.  No call, no value movement, no state change. -/
theorem executeCalls_empty
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    {srcC bh bundleM statusM : Literal}
    (hlen : evm.mload (evm.mload (bundleM + 160)) = 0) :
    execCall (fuel+3) fun_executeCalls []
        (Ok evm store, [srcC, bh, bundleM, statusM])
      = Ok evm store := by
  unfold execCall call fun_executeCalls
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, cons, cons, nil]
  simp only [Assign', LetEq', LetPrimCall', AssignPrimCall', If',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMAdd', EVMMload']
  have hok0 : isOk ((Ok evm store)☎️⟦["var_sourceChainId", "var_bundleHash",
      "var__interopBundle_mpos", "var_providedCallStatus_mpos"],
      [srcC, bh, bundleM, statusM]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["var_sourceChainId", "var_bundleHash",
      "var__interopBundle_mpos", "var_providedCallStatus_mpos"],
      [srcC, bh, bundleM, statusM]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have h3 : ((Ok evm store)☎️⟦["var_sourceChainId", "var_bundleHash",
      "var__interopBundle_mpos", "var_providedCallStatus_mpos"],
      [srcC, bh, bundleM, statusM]⟧)["var__interopBundle_mpos"]!! = bundleM :=
    lookup_initcall_3 (by decide) (by decide)
  rw [h3]
  simp only [evm_insert, hevm0]
  set I := (Ok evm store)☎️⟦["var_sourceChainId", "var_bundleHash",
      "var__interopBundle_mpos", "var_providedCallStatus_mpos"],
      [srcC, bh, bundleM, statusM]⟧
  have hokI : isOk I := hok0
  have hok1 : isOk (I⟦"_1" ↦ bundleM + 160⟧) := by
    rw [isOk_insert]; exact hokI
  rw [show (I⟦"_1" ↦ bundleM + 160⟧)["_1"]!! = bundleM + 160 from
    lookup_insert' hokI]
  have hok2 : isOk (I⟦"_1" ↦ bundleM + 160⟧⟦"split_expr_0" ↦
      evm.mload (bundleM + 160)⟧) := by
    rw [isOk_insert]; exact hok1
  rw [show (I⟦"_1" ↦ bundleM + 160⟧⟦"split_expr_0" ↦
      evm.mload (bundleM + 160)⟧)["split_expr_0"]!!
      = evm.mload (bundleM + 160) from lookup_insert' hok1]
  rw [hlen]
  have hok3 : isOk (I⟦"_1" ↦ bundleM + 160⟧⟦"split_expr_0" ↦
      evm.mload (bundleM + 160)⟧⟦"length" ↦ 0⟧) := by
    rw [isOk_insert]; exact hok2
  have hok4 : isOk (I⟦"_1" ↦ bundleM + 160⟧⟦"split_expr_0" ↦
      evm.mload (bundleM + 160)⟧⟦"length" ↦ 0⟧⟦"var_i" ↦ 0⟧) := by
    rw [isOk_insert]; exact hok3
  rw [For']
  dsimp only
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMLt', mkOk_of_isOk hok4]
  rw [show (I⟦"_1" ↦ bundleM + 160⟧⟦"split_expr_0" ↦
      evm.mload (bundleM + 160)⟧⟦"length" ↦ 0⟧⟦"var_i" ↦ 0⟧)["var_i"]!!
      = 0 from lookup_insert' hok3]
  rw [show (I⟦"_1" ↦ bundleM + 160⟧⟦"split_expr_0" ↦
      evm.mload (bundleM + 160)⟧⟦"length" ↦ 0⟧⟦"var_i" ↦ 0⟧)["length"]!!
      = 0 from by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_insert' hok2]
  try simp only [List.head!]
  try simp only [show fromBool ((0 : UInt256) < 0) = (0 : UInt256) from by decide]
  try simp only [reduceIte]
  try rw [if_pos (rfl : (0 : UInt256) = (0 : UInt256))]
  obtain ⟨e4, σ4, h4⟩ := State_of_isOk hok4
  have he4 : e4 = evm := by
    have h := congrArg State.evm h4
    rw [evm_insert, evm_insert, evm_insert, evm_insert, hevm0] at h
    exact h.symm
  rw [h4]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  rw [he4]

/-! ### The index-access helper: closed form for in-bounds reads -/

/-- **The call-array index access, in bounds**: with `index < mload(baseRef)`
the bounds panic is skipped and the call returns the element address
`baseRef + 32·index + 32`, evm untouched.  The loop step's first dependency. -/
lemma index_access_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {B I : Literal}
    {a : Identifier}
    (hlt : I < evm.mload B) :
    execCall (fuel+1) memory_array_index_access_enum_CallStatus_dyn [a]
        (Ok evm store, [B, I])
      = Ok evm (store.insert a (B + Fin.shiftLeft I 5 + 32)) := by
  unfold execCall call memory_array_index_access_enum_CallStatus_dyn
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  have hok0 : isOk ((Ok evm store)☎️⟦["baseRef", "index"], [B, I]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["baseRef", "index"], [B, I]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  set J := (Ok evm store)☎️⟦["baseRef", "index"], [B, I]⟧
  -- let split_expr_0 := mload(baseRef)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMload']
  rw [show J["baseRef"]!! = B from lookup_initcall_1]
  rw [hevm0]
  -- let split_expr_1 := lt(index, split_expr_0)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMLt']
  have hok1 : isOk (J⟦"split_expr_0" ↦ evm.mload B⟧) := by
    rw [isOk_insert]; exact hok0
  rw [show (J⟦"split_expr_0" ↦ evm.mload B⟧)["split_expr_0"]!! = evm.mload B from
    lookup_insert' hok0]
  rw [show (J⟦"split_expr_0" ↦ evm.mload B⟧)["index"]!! = I from by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_initcall_2 (by decide)]
  rw [show fromBool (I < evm.mload B) = (1 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_true hlt, if_true]]
  -- if iszero(split_expr_1) — skip
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  have hok2 : isOk (J⟦"split_expr_0" ↦ evm.mload B⟧⟦"split_expr_1" ↦ 1⟧) := by
    rw [isOk_insert]; exact hok1
  rw [show (J⟦"split_expr_0" ↦ evm.mload B⟧⟦"split_expr_1" ↦ 1⟧)["split_expr_1"]!!
      = 1 from lookup_insert' hok1]
  try rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- let split_expr_3 := shl(5, index)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl']
  rw [show (J⟦"split_expr_0" ↦ evm.mload B⟧⟦"split_expr_1" ↦ 1⟧)["index"]!! = I from by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact lookup_initcall_2 (by decide)]
  -- let split_expr_4 := add(baseRef, split_expr_3)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd']
  have hok3 : isOk (J⟦"split_expr_0" ↦ evm.mload B⟧⟦"split_expr_1" ↦ 1⟧⟦"split_expr_3" ↦ Fin.shiftLeft I 5⟧) := by
    rw [isOk_insert]; exact hok2
  rw [show (J⟦"split_expr_0" ↦ evm.mload B⟧⟦"split_expr_1" ↦ 1⟧⟦"split_expr_3" ↦ Fin.shiftLeft I 5⟧)["baseRef"]!! = B from by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
        lookup_insert_of_ne (by decide)]
    exact lookup_initcall_1]
  rw [show (J⟦"split_expr_0" ↦ evm.mload B⟧⟦"split_expr_1" ↦ 1⟧⟦"split_expr_3" ↦ Fin.shiftLeft I 5⟧)["split_expr_3"]!! = Fin.shiftLeft I 5 from
    lookup_insert' hok2]
  -- addr := add(split_expr_4, 32)
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd']
  have hok4 : isOk (J⟦"split_expr_0" ↦ evm.mload B⟧⟦"split_expr_1" ↦ 1⟧⟦"split_expr_3" ↦ Fin.shiftLeft I 5⟧⟦"split_expr_4" ↦ B + Fin.shiftLeft I 5⟧) := by
    rw [isOk_insert]; exact hok3
  rw [show (J⟦"split_expr_0" ↦ evm.mload B⟧⟦"split_expr_1" ↦ 1⟧⟦"split_expr_3" ↦ Fin.shiftLeft I 5⟧⟦"split_expr_4" ↦ B + Fin.shiftLeft I 5⟧)["split_expr_4"]!! = B + Fin.shiftLeft I 5 from
    lookup_insert' hok3]
  -- the ret lookup and the wrapper
  have hok5 : isOk (J⟦"split_expr_0" ↦ evm.mload B⟧⟦"split_expr_1" ↦ 1⟧⟦"split_expr_3" ↦ Fin.shiftLeft I 5⟧⟦"split_expr_4" ↦ B + Fin.shiftLeft I 5⟧⟦"addr" ↦ B + Fin.shiftLeft I 5 + 32⟧) := by
    rw [isOk_insert]; exact hok4
  rw [show (J⟦"split_expr_0" ↦ evm.mload B⟧⟦"split_expr_1" ↦ 1⟧⟦"split_expr_3" ↦ Fin.shiftLeft I 5⟧⟦"split_expr_4" ↦ B + Fin.shiftLeft I 5⟧⟦"addr" ↦ B + Fin.shiftLeft I 5 + 32⟧)["addr"]!! = B + Fin.shiftLeft I 5 + 32 from
    lookup_insert' hok4]
  obtain ⟨e5, σ5, h5⟩ := State_of_isOk hok5
  have he5 : e5 = evm := by
    have h := congrArg State.evm h5
    rw [evm_insert, evm_insert, evm_insert, evm_insert, evm_insert, hevm0] at h
    exact h.symm
  rw [h5]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [insert_Ok]
  rw [he5]

/-! ### The loop-step boundary doctrine and recipe

**Model fact (decisive for the step lemma's shape):** `EVMCall'` — like
`EVMStaticcall'` — is `primCall s .Call [...] = (s, [])`: an external call
returns NOTHING, so `let _7/_11 := call(...)` leaves the result variable
unbound and any subsequent read sees the lookup default `0`.  The model can
therefore express a failed call's aftermath (the `fail_forward_reverts`
family) but can NEVER drive past a *successful* one.  This is the same
boundary as #38's staticcall doctrine, now confirmed for the dispatch loop.

**Consequently the correct maximal per-iteration lemma is a PREFIX closed
form** — not an "oracle-pack" over call results:

`executeCalls_step_prefix` (zero-value, version-1, in-bounds, small-chain-id
iteration `i`): from the loop-entry state, the body executes deterministically
up to `_11 := call(gas, cleaned, _8, ...)`, pinning
- the element address (via `index_access_call`) and the struct reads,
- the version acceptance (`call_version_pass` values inline),
- the skipped value path (`_3 = 0` ⇒ the give-branch if is not entered),
- the per-call commitment `expr = keccak(bundleHash ‖ i)`
  (`primCall_keccakOut` + the accOut alignment, junk-window style),
- the formatted source address (`formatEvmV1_small_call`),
- the encoded payload and its extent (`abi_encode3_call`),
- the dispatch TARGET `cleaned = interopCall.to &&& 2^160-1` and VALUE
  `_8 = interopCall.value` as the call's argument values.

Everything after a successful dispatch — including the loop's continuation —
is outside the model (A8-class boundary); the failed-dispatch direction is
`dispatch_call_failure_forwards`.  All nine ingredient lemmas above are
proven; the prefix drive follows the formatEvmV1 assembly workflow
(recipe → counted peels → transcription). -/

/-! ### Step-prefix chunk arms -/

/-- Loop-body chunk 1: element address, struct pointer, first struct word,
version mask constant. -/
@[reducible] private def stepChunk1 : Stmt := <s
  {
      let split_expr_1 := mload(_1)
      let split_expr_2 := memory_array_index_access_enum_CallStatus_dyn(split_expr_1, var_i)
      let _mpos := mload(split_expr_2)
      let split_expr_3 := mload(_mpos)
      let split_expr_4 := shl(248, 255)
  }
>

/-- Loop-body chunk 2: the version-test values. -/
@[reducible] private def stepChunk2 : Stmt := <s
  {
      let split_expr_5 := and(split_expr_3, split_expr_4)
      let split_expr_6 := shl(248, 1)
      let split_expr_7 := eq(split_expr_5, split_expr_6)
  }
>

/-- **Chunk 1 closed form** (in-bounds): the element address is
`arr + 32·i + 32`, the struct pointer and first word are symbolic reads. -/
private lemma stepChunk1_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {BP I : Literal}
    (h1v : (Ok evm σ)["_1"]!! = BP)
    (hi : (Ok evm σ)["var_i"]!! = I)
    (hlt : I < evm.mload (evm.mload BP)) :
    exec (fuel+1) stepChunk1 (Ok evm σ)
      = Ok evm (((((σ.insert "split_expr_1" (evm.mload BP)).insert
          "split_expr_2" (evm.mload BP + Fin.shiftLeft I 5 + 32)).insert
          "_mpos" (evm.mload (evm.mload BP + Fin.shiftLeft I 5 + 32))).insert
          "split_expr_3" (evm.mload (evm.mload (evm.mload BP + Fin.shiftLeft I 5 + 32)))).insert
          "split_expr_4" (Fin.shiftLeft 255 248)) := by
  unfold stepChunk1
  -- let split_expr_1 := mload(_1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [h1v]
  -- let split_expr_2 := memory_array_index_access(...)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), hi]
  rw [index_access_call hlt]
  -- let _mpos := mload(split_expr_2)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  -- let split_expr_3 := mload(_mpos)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  -- let split_expr_4 := shl(248, 255)
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMShl',
             evm_Ok, setEvm_Ok, insert_Ok]

/-- **Chunk 2 closed form** (version accepted): the masked top byte equals
`INTEROP_CALL_VERSION`, so the test value is `1`. -/
private lemma stepChunk2_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {W : Literal}
    (h3 : (Ok evm σ)["split_expr_3"]!! = W)
    (h4 : (Ok evm σ)["split_expr_4"]!! = Fin.shiftLeft 255 248)
    (hver : Fin.land W (Fin.shiftLeft 255 248) = Fin.shiftLeft 1 248) :
    exec (fuel+1) stepChunk2 (Ok evm σ)
      = Ok evm (((σ.insert "split_expr_5" (Fin.shiftLeft 1 248)).insert
          "split_expr_6" (Fin.shiftLeft 1 248)).insert
          "split_expr_7" 1) := by
  unfold stepChunk2
  -- let split_expr_5 := and(split_expr_3, split_expr_4)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMAnd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [h3, h4]
  rw [hver]
  -- let split_expr_6 := shl(248, 1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMShl',
             evm_Ok, setEvm_Ok, insert_Ok]
  -- let split_expr_7 := eq(split_expr_5, split_expr_6)
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMEq',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  simp only [decide_eq_true (rfl : Fin.shiftLeft 1 248 = Fin.shiftLeft 1 248)]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  try simp only [show fromBool (decide True) = (1 : UInt256) from by decide]

/-- Loop-body target chunk: the dispatch target is the 160-bit-masked
`interopCall.to`. -/
@[reducible] private def stepTargetChunk : Stmt := <s
  {
      let split_expr_21 := add(_mpos, 64)
      let split_expr_22 := mload(split_expr_21)
      let split_expr_23 := shl(160, 1)
      let split_expr_24 := sub(split_expr_23, 1)
      let cleaned := and(split_expr_22, split_expr_24)
  }
>

/-- Loop-body staging chunk: call value read, commitment scratch (bundle hash
at the fresh pointer + 32). -/
@[reducible] private def stepStagingChunk : Stmt := <s
  {
      let _8 := mload(_2)
      let expr_mpos := mload(64)
      let _9 := add(expr_mpos, 32)
      mstore(_9, var_bundleHash)
      let split_expr_25 := add(expr_mpos, 64)
  }
>

/-- **Target chunk closed form**: `cleaned = mload(_mpos + 64) &&& (2^160-1)`
— the dispatch target formula, pinned. -/
private lemma stepTarget_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {MP : Literal}
    (hmp : (Ok evm σ)["_mpos"]!! = MP) :
    exec (fuel+1) stepTargetChunk (Ok evm σ)
      = Ok evm (((((σ.insert "split_expr_21" (MP + 64)).insert
          "split_expr_22" (evm.mload (MP + 64))).insert
          "split_expr_23" (Fin.shiftLeft 1 160)).insert
          "split_expr_24" (Fin.shiftLeft 1 160 - 1)).insert
          "cleaned" (Fin.land (evm.mload (MP + 64)) (Fin.shiftLeft 1 160 - 1))) := by
  unfold stepTargetChunk
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMAdd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [hmp]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMShl',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMSub',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMAnd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]

/-- **Staging chunk closed form**: the call value is read, the bundle hash is
staged at the fresh pointer's word slot. -/
private lemma stepStaging_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {M2 BH : Literal}
    (h2 : (Ok evm σ)["_2"]!! = M2)
    (hbh : (Ok evm σ)["var_bundleHash"]!! = BH) :
    exec (fuel+1) stepStagingChunk (Ok evm σ)
      = Ok (evm.mstore (evm.mload 64 + 32) BH)
          (((((σ.insert "_8" (evm.mload M2)).insert
            "expr_mpos" (evm.mload 64)).insert
            "_9" (evm.mload 64 + 32)).insert
            "split_expr_25" (evm.mload 64 + 64))) := by
  unfold stepStagingChunk
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [h2]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMAdd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hbh]
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMAdd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]

/-- Keccak primop under a known-hash hypothesis: the match collapses to the
success arm. -/
private lemma keccak_prim {e : EVMState} {σ : VarStore} {a b H : Literal}
    {ek : EVMState} (hk : e.keccak256 a b = some (H, ek)) :
    primCall (Ok e σ) .Keccak256 [a, b] = ((Ok e σ).setEvm ek, [H]) := by
  rw [EVMKeccak256']
  simp only [evm_Ok]
  rw [hk]

/-- Loop-body commitment chunk: stage the call index, the length word, bump
the free pointer past the 96-byte scratch, hash the 64-byte window
`bundleHash ‖ i`. -/
@[reducible] private def stepCommitChunk : Stmt := <s
  {
      mstore(split_expr_25, var_i)
      mstore(expr_mpos, 64)
      finalize_allocation(expr_mpos, 96)
      let split_expr_26 := mload(expr_mpos)
      let expr := keccak256(_9, split_expr_26)
  }
>

/-- Loop-body sender chunk: the formatted-sender source word is the
160-bit-masked `interopCall.from` (struct word at `_mpos + 96`). -/
@[reducible] private def stepSenderChunk : Stmt := <s
  {
      let split_expr_27 := add(_mpos, 96)
      let split_expr_28 := mload(split_expr_27)
      let split_expr_29 := shl(160, 1)
      let split_expr_30 := sub(split_expr_29, 1)
      let split_expr_31 := and(split_expr_28, split_expr_30)
  }
>

/-- **Commitment chunk closed form**: with `E₃` the post-staging memory
(`i` at `split25`, length `64` at `F`, free pointer at `F + 96`), the chunk
ends in the keccak-updated state with `expr = keccak(bundleHash ‖ i)`. -/
private lemma stepCommit_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {S25 I F N9 H : Literal}
    {ek : EVMState}
    (hs25 : (Ok evm σ)["split_expr_25"]!! = S25)
    (hF : (Ok evm σ)["expr_mpos"]!! = F)
    (hi : (Ok evm σ)["var_i"]!! = I)
    (h9 : (Ok evm σ)["_9"]!! = N9)
    (hf1 : ¬ (F + 96 > (18446744073709551615 : UInt256)))
    (hf2 : ¬ (F + 96 < F))
    (hk : (((evm.mstore S25 I).mstore F 64).mstore 64 (F + 96)).keccak256 N9
        ((((evm.mstore S25 I).mstore F 64).mstore 64 (F + 96)).mload F)
        = some (H, ek)) :
    exec (fuel+1) stepCommitChunk (Ok evm σ)
      = Ok ek ((σ.insert "split_expr_26"
          ((((evm.mstore S25 I).mstore F 64).mstore 64 (F + 96)).mload F)).insert
          "expr" H) := by
  unfold stepCommitChunk
  -- mstore(split_expr_25, var_i)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [hs25, hi]
  -- mstore(expr_mpos, 64)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_ok_evm _ evm, hF]
  -- finalize_allocation(expr_mpos, 96)
  rw [cons, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_ok_evm _ evm, hF]
  rw [finalize_alloc_call
    (by rw [show Fin.land ((96 : UInt256) + 31) (Clear.UInt256.lnot 31)
          = (96 : UInt256) from by decide]
        exact hf1)
    (by rw [show Fin.land ((96 : UInt256) + 31) (Clear.UInt256.lnot 31)
          = (96 : UInt256) from by decide]
        exact hf2)]
  rw [show Fin.land ((96 : UInt256) + 31) (Clear.UInt256.lnot 31)
    = (96 : UInt256) from by decide]
  -- let split_expr_26 := mload(expr_mpos)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_ok_evm _ evm, hF]
  -- let expr := keccak256(_9, split_expr_26)
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil,
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_ok_evm _ evm, h9]
  rw [keccak_prim hk]
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil,
             evm_Ok, setEvm_Ok, insert_Ok]

/-- **Sender chunk closed form**: `split_expr_31 = mload(_mpos + 96) &&&
(2^160-1)` — the formatted-sender source word, pinned. -/
private lemma stepSender_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {MP : Literal}
    (hmp : (Ok evm σ)["_mpos"]!! = MP) :
    exec (fuel+1) stepSenderChunk (Ok evm σ)
      = Ok evm (((((σ.insert "split_expr_27" (MP + 96)).insert
          "split_expr_28" (evm.mload (MP + 96))).insert
          "split_expr_29" (Fin.shiftLeft 1 160)).insert
          "split_expr_30" (Fin.shiftLeft 1 160 - 1)).insert
          "split_expr_31" (Fin.land (evm.mload (MP + 96)) (Fin.shiftLeft 1 160 - 1))) := by
  unfold stepSenderChunk
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMAdd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [hmp]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMShl',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMSub',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMAnd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]

end

end generated.L2InteropHandler.L2InteropHandler
