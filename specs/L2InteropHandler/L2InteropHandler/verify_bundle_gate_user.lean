import Clear.ReasoningPrinciple

import specs.KeccakDeterminism

/-
  THE BUNDLE-PROVENANCE ANCHOR (L2InteropHandler, `fun_verifyBundle`).

  `_verifyBundle`'s first guard (src 43:16378:16425) pins WHO may have sent
  the message the inclusion proof attests: the proof's `message.sender` must
  be the L2 InteropCenter built-in (`0x1000D = 65549`).  A bundle whose proof
  wraps a message from ANY other sender reverts before the inclusion check is
  even consulted — bundles cannot be smuggled in via foreign messages.
  Statements as in the source Yul (the generated fundef chunks them; the
  flat quote keeps the drive linear, semantics identical under Clear's flat
  store):

      let _1 := add(var_proof_mpos, 96)
      let cleaned := and(mload(add(mload(_1), 32)), sub(shl(160, 1), 1))
      … sum := 65549 …
      let cleaned_1 := and(sum, sub(shl(160, 1), 1))
      let cleaned_2 := and(mload(add(mload(_1), 32)), sub(shl(160, 1), 1))
      if iszero(eq(cleaned, cleaned_1)) { …revert(0, 68)… }

  * `ic_addr_mask` — the 160-bit mask leaves the InteropCenter address intact;
  * `verify_sender_pass` — an InteropCenter-sent message falls through;
  * `verify_sender_reverts` — any other sender REVERTS (`InvalidSender`).

  The memory words holding the sender stay SYMBOLIC (`evm.mload` terms) — no
  memory-layout claims are made.  Axiom-free.
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

/-! ### The sender guard, quoted verbatim (flat source shape) -/

/-- The message-sender guard of `fun_verifyBundle`. -/
private def senderGuard : Stmt := <s
  {
    let _1 := add(var_proof_mpos, 96)
    let cleaned := and(mload(add(mload(_1), 32)), sub(shl(160, 1), 1))
    let ret := 0
    let sum := 0
    sum := 65549
    let _2 := 0
    _2 := 0
    ret := sum
    let cleaned_1 := and(sum, sub(shl(160, 1), 1))
    let cleaned_2 := and(mload(add(mload(_1), 32)), sub(shl(160, 1), 1))
    if iszero(eq(cleaned, cleaned_1))
    {
        mstore(0, shl(225, 1157535291))
        mstore(4, cleaned_1)
        mstore(36, cleaned_2)
        revert(0, 68)
    }
}
>

/-- `and(65549, 2^160 - 1) = 65549`: the InteropCenter built-in address
(`0x1000D`) is untouched by the address mask. -/
theorem ic_addr_mask :
    Fin.land (65549 : UInt256) (Fin.shiftLeft 1 160 - 1) = 65549 := by decide

/-- The trailing guard if, as a named handle (quotes misresolve inside lemma
binder contexts — top-level def per the playbook). -/
@[reducible] private def senderIf : Stmt := <s
  if iszero(eq(cleaned, cleaned_1))
  {
      mstore(0, shl(225, 1157535291))
      mstore(4, cleaned_1)
      mstore(36, cleaned_2)
      revert(0, 68)
  }
>

/-- The shared statement drive up to the guard if: returns the full let tower.
Both directions branch only at the final if. -/
private lemma senderGuard_prefix_drive
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {Pv : Literal}
    (hP : (Ok evm store)["var_proof_mpos"]!! = Pv) :
    exec (fuel+1) senderGuard (Ok evm store)
      = exec (fuel+1) senderIf
        (Ok evm ((((((((((store.insert "_1" (Pv + 96)).insert
            "cleaned" (Fin.land (evm.mload (evm.mload (Pv + 96) + 32))
              (Fin.shiftLeft 1 160 - 1))).insert
            "ret" 0).insert "sum" 0).insert "sum" 65549).insert
            "_2" 0).insert "_2" 0).insert "ret" 65549).insert
            "cleaned_1" (Fin.land 65549 (Fin.shiftLeft 1 160 - 1))).insert
            "cleaned_2" (Fin.land (evm.mload (evm.mload (Pv + 96) + 32))
              (Fin.shiftLeft 1 160 - 1)))) := by
  unfold senderGuard
  -- let _1 := add(var_proof_mpos, 96)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  try simp only [List.head!]
  rw [hP]
  -- let cleaned := and(mload(add(mload(_1), 32)), sub(shl(160, 1), 1))
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMMload', EVMAdd', EVMSub', EVMShl', EVMAnd', evm_Ok, insert_Ok]
  try simp only [List.head!]
  rw [lookup_insert_self_fin]
  -- let ret := 0 / let sum := 0
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  -- sum := 65549
  rw [cons, Assign']
  simp only [Lit', insert_Ok]
  -- let _2 := 0 / _2 := 0
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  rw [cons, Assign']
  simp only [Lit', insert_Ok]
  -- ret := sum
  rw [cons, Assign']
  simp only [Var', insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  -- let cleaned_1 := and(sum, sub(shl(160, 1), 1))
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMSub', EVMShl', EVMAnd', insert_Ok]
  try simp only [List.head!]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  -- let cleaned_2 := and(mload(add(mload(_1), 32)), sub(shl(160, 1), 1))
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMMload', EVMAdd', EVMSub', EVMShl', EVMAnd', evm_Ok, insert_Ok]
  try simp only [List.head!]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  -- expose the trailing if
  rw [cons, nil]

/-- **AN INTEROPCENTER MESSAGE PASSES**: when the proof's masked
`message.sender` IS the InteropCenter built-in, the guard falls through with
the evm unchanged. -/
theorem verify_sender_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {Pv : Literal}
    (hP : (Ok evm store)["var_proof_mpos"]!! = Pv)
    (hsender : Fin.land (evm.mload (evm.mload (Pv + 96) + 32))
        (Fin.shiftLeft 1 160 - 1) = (65549 : UInt256)) :
    ∃ σ' : VarStore,
      exec (fuel+1) senderGuard (Ok evm store) = Ok evm σ' := by
  rw [senderGuard_prefix_drive hP]
  unfold senderIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero', EVMEq']
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [ic_addr_mask]
  rw [show fromBool (Fin.land (evm.mload (evm.mload (Pv + 96) + 32))
        (Fin.shiftLeft 1 160 - 1) = (65549 : UInt256)) = (1 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_true hsender, if_true]]
  try simp only [List.head!]
  rw [if_neg (by decide : ¬ (fromBool (decide ((1 : UInt256) = 0)) ≠ (0 : UInt256)))]
  exact ⟨_, rfl⟩

/-- **ANY OTHER SENDER REVERTS**: a proof wrapping a message whose masked
sender is NOT the InteropCenter cannot reach the inclusion check — the guard
REVERTS with `InvalidSender`.  Bundles cannot be delivered via messages of
foreign provenance. -/
theorem verify_sender_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {Pv : Literal}
    (hP : (Ok evm store)["var_proof_mpos"]!! = Pv)
    (hsender : Fin.land (evm.mload (evm.mload (Pv + 96) + 32))
        (Fin.shiftLeft 1 160 - 1) ≠ (65549 : UInt256)) :
    (exec (fuel+1) senderGuard (Ok evm store)).evm.reverted = true := by
  rw [senderGuard_prefix_drive hP]
  unfold senderIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero', EVMEq']
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [ic_addr_mask]
  rw [show fromBool (Fin.land (evm.mload (evm.mload (Pv + 96) + 32))
        (Fin.shiftLeft 1 160 - 1) = (65549 : UInt256)) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hsender, if_false]]
  try simp only [List.head!]
  rw [if_pos (by decide : fromBool (decide True) ≠ (0 : UInt256))]
  -- mstore(0, shl(225, 1157535291))
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMShl', EVMMstore', evm_Ok, setEvm_Ok]
  try simp only [List.head!]
  -- mstore(4, cleaned_1) / mstore(36, cleaned_2)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMMstore', evm_Ok, setEvm_Ok]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMMstore', evm_Ok, setEvm_Ok]
  -- revert(0, 68)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMRevert', evm_Ok, setEvm_Ok]
  rfl

/-! ### The inclusion gate: the attested-inclusion bool must be true -/

/-- The final gate of `fun_verifyBundle`: `expr` is the bool decoded from the
`proveL2MessageInclusionShared` staticcall to the L2 message-verification
built-in (`0x10009 = 65545`, the trust anchor); reject unless it is true
(selector `0x196170ab = 425816235`, `MessageVerificationFailed`). -/
@[reducible] private def inclusionIf : Stmt := <s
  if iszero(expr)
  {
      mstore(0, shl(225, 425816235))
      revert(0, 4)
  }
>

/-- **VERIFIED INCLUSION PASSES**: a true attested-inclusion bool falls
through with the state unchanged. -/
theorem inclusion_verified_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {b : Literal}
    (hb : (Ok evm store)["expr"]!! = b) (hb0 : b ≠ 0) :
    exec (fuel+1) inclusionIf (Ok evm store) = Ok evm store := by
  unfold inclusionIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [hb]
  rw [show fromBool (b = 0) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hb0, if_false]]
  simp only [List.head!]
  rw [if_neg (by exact fun h => h rfl)]

/-- **UNVERIFIED INCLUSION REVERTS**: if the message-verification system
contract does NOT attest the message's inclusion (`expr = 0`), the bundle is
rejected with `MessageVerificationFailed` — no unattested bundle is ever
executed.  The staticcall itself is the model's opaque external-call
boundary; `expr` carries its decoded verdict (#38-style decomposition). -/
theorem inclusion_unverified_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hb : (Ok evm store)["expr"]!! = 0) :
    (exec (fuel+1) inclusionIf (Ok evm store)).evm.reverted = true := by
  unfold inclusionIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [hb]
  try rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- mstore(0, shl(225, 425816235))
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

end

end generated.L2InteropHandler.L2InteropHandler
