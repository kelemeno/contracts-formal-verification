import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5326885561126133312
import generated.AtomicFlowManager.AtomicFlowManager.cleanup_bool
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_uint256_7396
import specs.AtomicFlowManager.AtomicFlowManager.imt_path_user
import specs.AtomicFlowManager.AtomicFlowManager.imt_path_toplevel_user

/-
  THE INCLUSION GATE OF `fun_verifyInclusion` — no delivery without a genuine
  Merkle inclusion proof (bridge-spec point 2/4, the "delivered" arm).

  `verifyInclusion` ends with:
      split_expr_14 := fun_calculateRootMemory(var_proof_mpos, value_1, split_expr_13)
      var           := eq(split_expr_14, value)
      split_expr_15 := iszero(var)
      if cleanup_bool(split_expr_15) { … revert }         -- if_5326885561126133312

  With `calculateRootMemory_call` (= pure `foldRoot`, #24) this file proves:
  if the recomputed root `foldRoot(evm, proof, depth, 0, index, leafHash)` does
  NOT equal the authenticated root (`value`), the gate REVERTS.  Contrapositive:
  a delivery can only be accepted when the submitted proof folds to exactly the
  authenticated IMT root — an attacker cannot finalize a leg with a crafted
  proof for a leaf that is not in the committed tree (modulo keccak collisions,
  which are not assumed here: this direction is determinism-only, axiom-free).
-/

namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     AtomicFlowManager.Common

set_option maxRecDepth 6000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-- `insert` on an `Ok` state writes into the underlying varstore. -/
@[simp] private lemma insert_Ok {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

private lemma evm_setEvm_of_isOk {s : State} {e : EVMState} (h : isOk s) :
    (s.setEvm e).evm = e := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma reviveJump_of_isOk {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma lookup_setEvm_of_isOk {s : State} {e : EVMState} {k : Identifier}
    (h : isOk s) : (s.setEvm e)[k]!! = s[k]!! := by
  obtain ⟨evm₀, st, rfl⟩ := State_of_isOk h; rfl

private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok]; exact lookup_insert_of_ne h

private lemma lookup_ok_evm {e e' : EVMState} {σ : VarStore} {k : Identifier} :
    (Ok e σ)[k]!! = (Ok e' σ)[k]!! := rfl

private lemma evm_Ok {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

private lemma setEvm_Ok {e e' : EVMState} {σ : VarStore} :
    (Ok e σ).setEvm e' = Ok e' σ := rfl

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

/-- Closed form of the revert-payload encoder `abi_encode_uint256_uint256_7396`:
`tail := 68; mstore(4, v0); mstore(36, v1)` — pure memory effect, returns 68. -/
lemma abi7396_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {v0 v1 : Literal} {t : Identifier} :
    execCall (fuel+1) abi_encode_uint256_uint256_7396 [t] (Ok evm store, [v0, v1])
      = Ok ((evm.mstore 4 v0).mstore 36 v1) (store.insert t 68) := by
  unfold execCall call abi_encode_uint256_uint256_7396
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, nil]
  simp only [Assign', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMstore']
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
  -- second mstore argument
  have hok2 : isOk (((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧⟦"tail" ↦ 68⟧).setEvm
      (evm.mstore 4 v0)) := by
    rw [isOk_setEvm]; exact hok1
  have hv1l : (((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧⟦"tail" ↦ 68⟧).setEvm
      (evm.mstore 4 v0))["value1"]!! = v1 := by
    rw [lookup_setEvm_of_isOk hok1, lookup_insert_of_ne (by decide)]
    exact lookup_initcall_2 (by decide)
  rw [hv1l]
  rw [evm_setEvm_of_isOk hok1]
  -- the `tail` return lookup on the final state
  have hok3 : isOk ((((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧⟦"tail" ↦ 68⟧).setEvm
      (evm.mstore 4 v0)).setEvm ((evm.mstore 4 v0).mstore 36 v1)) := by
    rw [isOk_setEvm]; exact hok2
  have htail : ((((Ok evm store)☎️⟦["value0", "value1"], [v0, v1]⟧⟦"tail" ↦ 68⟧).setEvm
      (evm.mstore 4 v0)).setEvm ((evm.mstore 4 v0).mstore 36 v1))["tail"]!! = 68 := by
    rw [lookup_setEvm_of_isOk hok2, lookup_setEvm_of_isOk hok1]
    exact lookup_insert' hok0
  rw [htail]
  obtain ⟨e3, σ3, h3⟩ := State_of_isOk hok3
  have he3 : e3 = (evm.mstore 4 v0).mstore 36 v1 := by
    have h := congrArg State.evm h3
    rw [evm_setEvm_of_isOk hok2] at h
    exact h.symm
  rw [h3]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [insert_Ok]
  rw [he3]

/-- Closed form of `cleanup_bool(x) = iszero(iszero(x))` at the eval level:
pure, returns the booleanization of `x`. -/
lemma cleanup_bool_evalCall
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x : Literal} :
    evalCall (fuel+1) cleanup_bool (Ok evm store, [x])
      = (Ok evm store, fromBool (fromBool (x = 0) = 0)) := by
  unfold evalCall call cleanup_bool
  simp only [params, body, rets, mkOk_initcall_Ok, List.map_nil, List.map_cons]
  rw [cons, cons, nil]
  simp only [LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero', multifill_cons, multifill_nil]
  rw [lookup_initcall_1]
  rw [lookup_insert' (by apply isOk_initcall_of_isOk; trivial)]
  have hok0 : isOk ((Ok evm store)☎️⟦["value"], [x]⟧) := isOk_initcall_of_isOk trivial
  have hok2 : isOk ((Ok evm store)☎️⟦["value"], [x]⟧⟦"split_expr_0" ↦ fromBool (x = 0)⟧⟦"cleaned"
      ↦ fromBool (fromBool (x = 0) = 0)⟧) := by
    rw [isOk_insert, isOk_insert]; exact hok0
  rw [reviveJump_of_isOk hok2]
  simp only [overwrite?_of_Ok]
  rw [lookup_insert' (by rw [isOk_insert]; exact hok0)]
  have hevm0 : ((Ok evm store)☎️⟦["value"], [x]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  obtain ⟨e2, σ2, h2⟩ := State_of_isOk hok2
  have he2 : e2 = evm := by
    have h := congrArg State.evm h2
    rw [evm_insert, evm_insert, hevm0] at h
    exact h.symm
  rw [h2, setStore_ok, he2]
  simp only [List.head!]

/-- The guard-if `if_5326885561126133312` REVERTS whenever `split_expr_15 = 1`
(the root comparison failed): `cleanup_bool(1) = 1`, the body encodes the
error payload and calls `revert(0, 68)`. -/
lemma gate_if_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hcond : (Ok evm store)["split_expr_15"]!! = 1) :
    (exec (fuel+1) if_5326885561126133312 (Ok evm store)).evm.reverted = true := by
  unfold if_5326885561126133312
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var',
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append]
  rw [Call']
  simp only [evalArgs, evalTail, cons', reverse',
             Lit', Var', List.reverse_cons, List.reverse_nil,
             List.nil_append, List.singleton_append]
  rw [hcond, cleanup_bool_evalCall]
  rw [show fromBool (fromBool ((1 : UInt256) = 0) = 0) = (1 : UInt256) from by decide]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- body statement 1: split_expr_16 := shl(226, 571374107)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- body statement 2: mstore(0, split_expr_16)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  -- body statement 3: split_expr_17 := abi_encode_uint256_uint256_7396(value, var_commitValue)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [abi7396_call]
  -- body statement 4: revert(0, split_expr_17)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMRevert',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rfl

/-- **THE INCLUSION GATE REVERTS ON A ROOT MISMATCH.**  Running the tail of
`fun_verifyInclusion` — the `calculateRootMemory` call, the root comparison and
the guard-if — from any state where the submitted proof does NOT fold to the
authenticated root ends with `reverted = true`.  (Axiom-free: this direction
needs only hash determinism, not injectivity.)  Hypotheses `hlt256 … hdepthlt`
are the success-path guards of `calculateRootMemory` itself — if THEY fail the
inner call already reverts, so either way no delivery happens. -/
theorem inclusion_root_mismatch_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {s₉ : State}
    {proofPos idxv leafv rootv : Literal}
    (hproof : (Ok evm store)["var_proof_mpos"]!! = proofPos)
    (hidxv  : (Ok evm store)["value_1"]!! = idxv)
    (hleafv : (Ok evm store)["split_expr_13"]!! = leafv)
    (hrootv : (Ok evm store)["value"]!! = rootv)
    (hlt256 : evm.mload proofPos < 256)
    (hidx : idxv < Fin.shiftLeft (1 : UInt256) (evm.mload proofPos))
    (hfuel : 2 * (evm.mload proofPos).val + 2 ≤ fuel)
    (hpath96 : 96 ≤ proofPos.val)
    (hnw : proofPos.val + 32 * (evm.mload proofPos).val + 64 ≤ 2 ^ 256)
    (hdepthlt : (evm.mload proofPos).val < 2 ^ 64)
    (hmismatch : (foldRoot evm proofPos (evm.mload proofPos).val 0 idxv leafv).1 ≠ rootv)
    (hexec : exec (fuel+1) (.Block
        [LetCall ["split_expr_14"] fun_calculateRootMemory
           [Var "var_proof_mpos", Var "value_1", Var "split_expr_13"],
         AssignPrimCall ["var"] P.Eq [Var "split_expr_14", Var "value"],
         LetPrimCall ["split_expr_15"] P.Iszero [Var "var"],
         if_5326885561126133312]) (Ok evm store) = s₉) :
    s₉.evm.reverted = true := by
  rw [← hexec]
  -- statement 1: split_expr_14 := fun_calculateRootMemory(proof, index, leafHash)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append]
  rw [hproof, hidxv, hleafv]
  rw [calculateRootMemory_call hlt256 hidx hfuel hpath96 hnw hdepthlt]
  -- statement 2: var := eq(split_expr_14, value)
  rw [cons, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMEq', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide)]
  rw [lookup_ok_evm (e' := evm), hrootv]
  rw [show fromBool ((foldRoot evm proofPos (evm.mload proofPos).val 0 idxv leafv).1 = rootv)
      = (0 : UInt256) from by rw [decide_eq_false hmismatch]; rfl]
  simp only [insert_Ok]
  -- statement 3: split_expr_15 := iszero(var)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  simp only [insert_Ok]
  -- statement 4: the guard-if reverts (split_expr_15 = 1)
  rw [cons, nil]
  exact gate_if_reverts (by rw [lookup_insert_self_fin])

end

end generated.AtomicFlowManager.AtomicFlowManager
