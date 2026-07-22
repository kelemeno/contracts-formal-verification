import Clear.ReasoningPrinciple

import specs.KeccakDeterminism

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

end

end generated.L2InteropHandler.L2InteropHandler
