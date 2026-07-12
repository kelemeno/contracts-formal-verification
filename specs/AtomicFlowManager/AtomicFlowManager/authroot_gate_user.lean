import Clear.ReasoningPrinciple

import specs.AtomicFlowManager.AtomicFlowManager.inclusion_gate_user
import generated.AtomicFlowManager.AtomicFlowManager.fun_authenticateRoot

/-
  THE ROOT-AUTHENTICATION GUARDS — acceptance anchors the metadata.

  `fun_authenticateRoot` (called by BOTH gates for every proof) verifies the
  commitment tree's root message against the L2 message-verification
  system contract and re-parses the same proof for the settlement-layer
  metadata `(slBlock, slChainId, batchTimestamp)` that the temporal guards
  (#36) then consume.  Its two semantic guards, quoted verbatim:

  * **root verified** — the `proveL2MessageInclusionShared` staticcall's
    decoded result must be TRUE, else `ProofRootNotVerified`;
  * **multi-hop only** — a single-level / commit-based proof
    (`finalProofNode = true`) carries no settlement-layer anchor and is
    REJECTED, else the `l1Timestamp` fed to the deadline comparisons could
    not be trusted to sit on the flow's settlement-layer clock.

  Both proven in both directions.  Acceptance of `authenticateRoot` thus
  means: the root really is the one the commitment tree published (modulo
  the message-verification system contract — the cross-chain trust anchor),
  and the timestamp/chain metadata come from a parsed SL anchor.

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

/-! ### The two guard blocks, quoted verbatim from the body -/

/-- The root-verification guard: revert `ProofRootNotVerified` unless the
message-verification staticcall's decoded result is true. -/
private def rootGuard : Stmt := <s
  if iszero(expr_2)
{
    let split_expr_19 := shl(227, 263661895)
    mstore(0, split_expr_19)
    let split_expr_20 := abi_encode_uint256_uint256_7396(value_1, value_2)
    revert(0, split_expr_20)
}
>

/-- The multi-hop guard: revert unless `finalProofNode = false` (a
single-level proof exposes no settlement-layer anchor). -/
private def hopGuard : Stmt := <s
  if cleanup_bool(split_expr_23)
{
    let split_expr_24 := shl(224, 1192991499)
    mstore(0, split_expr_24)
    let split_expr_25 := abi_encode_uint256_uint256_7396(value_1, value_2)
    revert(0, split_expr_25)
}
>

/-! ### Guard 1 — the root message is verified -/

/-- **PASS**: the verification result is nonzero (true) — the root message
was attested; the guard falls through with the state unchanged. -/
theorem root_verified_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {b : Literal}
    (hb : (Ok evm store)["expr_2"]!! = b)
    (hne : b ≠ 0) :
    exec (fuel+1) rootGuard (Ok evm store) = Ok evm store := by
  unfold rootGuard
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [hb]
  rw [show fromBool (b = 0) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hne, if_false]]
  simp only [List.head!]
  rw [if_neg (by exact fun h => h rfl)]

/-- **REVERT**: the verification result is zero (false) — the root is NOT
attested by the message-verification contract; nothing downstream runs. -/
theorem root_unverified_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hb : (Ok evm store)["expr_2"]!! = 0) :
    (exec (fuel+1) rootGuard (Ok evm store)).evm.reverted = true := by
  unfold rootGuard
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [hb]
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
  -- body: mstore(0, split_expr_19)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  -- body: split_expr_20 := abi_encode_uint256_uint256_7396(...)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [abi7396_call]
  -- body: revert(0, split_expr_20)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMRevert',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rfl

/-! ### Guard 2 — the proof is multi-hop (has a settlement-layer anchor) -/

/-- **PASS**: `finalProofNode = 0` — the proof exposes the settlement-layer
metadata; the guard falls through with the state unchanged. -/
theorem multihop_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hf : (Ok evm store)["split_expr_23"]!! = 0) :
    exec (fuel+1) hopGuard (Ok evm store) = Ok evm store := by
  unfold hopGuard
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var',
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append]
  rw [Call']
  simp only [evalArgs, evalTail, cons', reverse',
             Lit', Var', List.reverse_cons, List.reverse_nil,
             List.nil_append, List.singleton_append]
  rw [hf, cleanup_bool_evalCall]
  rw [show fromBool (fromBool ((0 : UInt256) = 0) = 0) = (0 : UInt256) from by decide]
  rw [if_neg (by exact fun h => h rfl)]

/-- **REVERT**: `finalProofNode = 1` — a single-level proof with no
settlement-layer anchor is rejected: the deadline clock cannot be forged
by a proof that never touched the settlement layer. -/
theorem final_node_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hf : (Ok evm store)["split_expr_23"]!! = 1) :
    (exec (fuel+1) hopGuard (Ok evm store)).evm.reverted = true := by
  unfold hopGuard
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var',
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append]
  rw [Call']
  simp only [evalArgs, evalTail, cons', reverse',
             Lit', Var', List.reverse_cons, List.reverse_nil,
             List.nil_append, List.singleton_append]
  rw [hf, cleanup_bool_evalCall]
  rw [show fromBool (fromBool ((1 : UInt256) = 0) = 0) = (1 : UInt256) from by decide]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- body: shl let
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- body: mstore(0, split_expr_24)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  -- body: split_expr_25 := abi_encode_uint256_uint256_7396(...)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [abi7396_call]
  -- body: revert(0, split_expr_25)
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
