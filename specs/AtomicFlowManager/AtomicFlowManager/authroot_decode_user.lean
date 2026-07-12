import Clear.ReasoningPrinciple

import specs.AtomicFlowManager.AtomicFlowManager.inclusion_gate_user
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bool_fromMemory
import generated.AtomicFlowManager.AtomicFlowManager.validator_revert_bool

/-
  THE VERIFICATION-RESULT DECODE BOUNDARY.

  Clear models external calls as opaque: the `staticcall` PRIMOP returns no
  values (`EVMStaticcall' : primCall s .Staticcall [...] = (s, [])`), so the
  message-verification call's RESULT cannot be computed inside the model —
  it enters the proofs as a hypothesis (exactly how #38's guards are
  stated).  What CAN be verified is the decode boundary around it: whatever
  word the verifier wrote to the return area, the decoded flag `expr_2` is
  that word read back and VALIDATED boolean — a non-boolean return word
  reverts, so #38's `expr_2 ≠ 0` hypothesis is precisely "the verifier
  returned true", with no third possibility.

  * `validator_bool_pass` / `validator_nonbool_reverts` —
    `validator_revert_bool` accepts exactly the boolean words `{0, 1}`.

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

/-! ### The boolean validator: pass and revert -/

/-- The pass core, symbolically: if the word equals its own booleanization,
the validator falls through with the state unchanged. -/
private lemma validator_pass_core
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x : Literal}
    (hself : fromBool (x = fromBool (fromBool (x = 0) = 0)) = (1 : UInt256)) :
    execCall (fuel+1) validator_revert_bool [] (Ok evm store, [x])
      = Ok evm store := by
  unfold execCall call validator_revert_bool
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, cons, nil]
  simp only [If', LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMEq']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["value"], [x]⟧) := isOk_initcall_of_isOk trivial
  obtain ⟨e0, σ0, h0⟩ := State_of_isOk hok0
  have he0 : e0 = evm := by
    have hq := congrArg State.evm h0
    rw [show (((Ok evm store)☎️⟦["value"], [x]⟧)).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at hq
    exact hq.symm
  have hxl : ((Ok evm store)☎️⟦["value"], [x]⟧)["value"]!! = x := lookup_initcall_1
  rw [h0, he0] at hxl
  simp only [h0, he0, insert_Ok]
  simp only [hxl]
  have e1 : (Ok evm (Finmap.insert "split_expr_0" (fromBool (x = 0)) σ0))["split_expr_0"]!!
      = fromBool (x = 0) := lookup_insert_self_fin
  simp only [e1]
  have e2 : (Ok evm (Finmap.insert "split_expr_1" (fromBool (fromBool (x = 0) = 0))
      (Finmap.insert "split_expr_0" (fromBool (x = 0)) σ0)))["value"]!! = x := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact hxl
  have e3 : (Ok evm (Finmap.insert "split_expr_1" (fromBool (fromBool (x = 0) = 0))
      (Finmap.insert "split_expr_0" (fromBool (x = 0)) σ0)))["split_expr_1"]!!
      = fromBool (fromBool (x = 0) = 0) := lookup_insert_self_fin
  simp only [e2, e3]
  simp only [hself]
  have e4 : (Ok evm (Finmap.insert "split_expr_2" (1 : UInt256)
      (Finmap.insert "split_expr_1" (fromBool (fromBool (x = 0) = 0))
        (Finmap.insert "split_expr_0" (fromBool (x = 0)) σ0))))["split_expr_2"]!!
      = (1 : UInt256) := lookup_insert_self_fin
  simp only [e4]
  simp only [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  simp only [List.head!]
  rw [if_neg (by exact fun h => h rfl)]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]

/-- **PASS**: a boolean word (`0` or `1`) passes the validator unchanged. -/
theorem validator_bool_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x : Literal}
    (hb : x = 0 ∨ x = 1) :
    execCall (fuel+1) validator_revert_bool [] (Ok evm store, [x])
      = Ok evm store := by
  rcases hb with rfl | rfl
  · exact validator_pass_core (by decide)
  · exact validator_pass_core (by decide)

/-- **REVERT**: a non-boolean return word is rejected — the decoded flag has
no third value. -/
theorem validator_nonbool_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x : Literal}
    (hne0 : x ≠ 0) (hne1 : x ≠ 1) :
    ((execCall (fuel+1) validator_revert_bool [] (Ok evm store, [x])).evm).reverted
      = true := by
  have h1 : fromBool (x = 0) = (0 : UInt256) := by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hne0, if_false]
  have hself : fromBool (x = fromBool (fromBool (x = 0) = 0)) = (0 : UInt256) := by
    rw [h1]
    rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
    simp only [fromBool, Bool.toUInt256, decide_eq_false hne1, if_false]
  unfold execCall call validator_revert_bool
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, cons, nil]
  simp only [If', LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMEq']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["value"], [x]⟧) := isOk_initcall_of_isOk trivial
  obtain ⟨e0, σ0, h0⟩ := State_of_isOk hok0
  have he0 : e0 = evm := by
    have hq := congrArg State.evm h0
    rw [show (((Ok evm store)☎️⟦["value"], [x]⟧)).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at hq
    exact hq.symm
  have hxl : ((Ok evm store)☎️⟦["value"], [x]⟧)["value"]!! = x := lookup_initcall_1
  rw [h0, he0] at hxl
  simp only [h0, he0, insert_Ok]
  simp only [hxl]
  have e1 : (Ok evm (Finmap.insert "split_expr_0" (fromBool (x = 0)) σ0))["split_expr_0"]!!
      = fromBool (x = 0) := lookup_insert_self_fin
  simp only [e1]
  have e2 : (Ok evm (Finmap.insert "split_expr_1" (fromBool (fromBool (x = 0) = 0))
      (Finmap.insert "split_expr_0" (fromBool (x = 0)) σ0)))["value"]!! = x := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact hxl
  have e3 : (Ok evm (Finmap.insert "split_expr_1" (fromBool (fromBool (x = 0) = 0))
      (Finmap.insert "split_expr_0" (fromBool (x = 0)) σ0)))["split_expr_1"]!!
      = fromBool (fromBool (x = 0) = 0) := lookup_insert_self_fin
  simp only [e2, e3]
  simp only [hself]
  have e4 : (Ok evm (Finmap.insert "split_expr_2" (0 : UInt256)
      (Finmap.insert "split_expr_1" (fromBool (fromBool (x = 0) = 0))
        (Finmap.insert "split_expr_0" (fromBool (x = 0)) σ0))))["split_expr_2"]!!
      = (0 : UInt256) := lookup_insert_self_fin
  simp only [e4]
  try simp only [List.head!]
  -- body: revert(0, 0)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMRevert',
             evm_Ok, setEvm_Ok]
  rfl

end

end generated.AtomicFlowManager.AtomicFlowManager
