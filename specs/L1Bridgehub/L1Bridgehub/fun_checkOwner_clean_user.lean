import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_7506504477940969768

import generated.L1Bridgehub.L1Bridgehub.fun_checkOwner_gen

import specs.L1Bridgehub.L1Bridgehub.fun_checkOwner_user

import specs.RevertModel

/-
  CLEAN guard theorem for `fun_checkOwner` (OpenZeppelin `Ownable._checkOwner`),
  enabled by the new `reverted` flag on `EVMState`.

  Old form (fun_checkOwner_user.lean): the spec could only state that the guard
  literal *computes* the right boolean `owner == caller`, because in this EVM
  model a `revert` still left the state `Ok` — so a successful run and a
  reverting run were indistinguishable by `isOk`.

  New form (here): with the `reverted` flag, a NON-reverting (i.e. genuinely
  successful) execution of `checkOwner` IMPLIES the caller is the owner.  This is
  the faithful "success ⇒ precondition held" reading of
      require(owner() == _msgSender()).
-/

namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common Clear.RevertModel

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/--
  Reverted behaviour of the owner-check if-block, proved by direct replay.

  Running `if iszero(split_expr_4) { …; revert(…) }` on `Ok evm store`:
    * if the guard `split_expr_4` is nonzero (owner == caller): the body is
      skipped, the result is the unchanged `Ok evm store`, whose `reverted`
      flag is `evm.reverted`;
    * if the guard is `0` (owner ≠ caller): the body runs and ends in
      `revert`, forcing `reverted = true`.

  Hence, for the output state `s₉`, `s₉.evm.reverted = true` UNLESS the guard
  was nonzero.  We state the contrapositive we need: a non-reverting output
  (given a non-reverting input) forces the guard nonzero.
-/
lemma if_owner_reverted_iff
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hr : evm.reverted = false) :
    (🧟(exec fuel if_7506504477940969768 (Ok evm store))).evm.reverted = false →
      (Ok evm store)["split_expr_4"]!! ≠ 0 := by
  unfold if_7506504477940969768
  rw [If']
  -- evaluate the guard `iszero(split_expr_4)`
  simp only [evalArgs, head', reverse', multifill', PrimCall', Lit', Var',
             execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil,
             List.nil_append, List.singleton_append, evalTail, cons']
  rw [EVMIszero']
  simp only [head', List.head!]
  -- case split on whether the guard literal is zero
  by_cases hz : (Ok evm store)["split_expr_4"]!! = 0
  · -- guard zero ⇒ body runs ⇒ ends in revert ⇒ reverted = true, contradiction
    intro hcontra
    exfalso
    revert hcontra
    -- `iszero 0 = 1 ≠ 0`, so the `if` takes the then-branch (body)
    simp only [hz, fromBool, decide_True, Bool.toUInt256, cond_true]
    rw [if_pos (by decide : ((if True then (1 : UInt256) else 0)) ≠ 0)]
    -- replay the body; every statement is a primop, the last being `revert`.
    simp only [cons, nil, ExprStmtPrimCall', LetPrimCall', AssignPrimCall',
               evalArgs, evalTail, cons', head', reverse', multifill',
               PrimCall', Lit', Var', execPrimCall, evalPrimCall,
               List.reverse_cons, List.reverse_nil, List.nil_append,
               List.singleton_append, List.append_assoc, List.cons_append,
               EVMMload', EVMShl', EVMMstore', EVMAdd', EVMRevert']
    -- the final state is `setEvm (evm_revert …) (Ok … )`, so reverted = true.
    -- `setEvm` over an Ok-shaped state writes the evm verbatim, and
    -- `evm_revert` sets `reverted := true`; hence the flag is `true`, never `false`.
    intro hbad
    exact absurd hbad (by simp only [Bool.not_eq_false]; rfl)
  · -- guard nonzero ⇒ thesis is exactly `hz`
    intro _
    exact hz

/-- The inlined owner-check `If` statement in `fun_checkOwner`'s body is exactly
    the named if-block `if_7506504477940969768` (definitional unfolding). -/
lemma checkOwner_if_eq :
    (Stmt.If (Expr.PrimCall P.Iszero [Expr.Var "split_expr_4"])
        [Stmt.LetPrimCall ["memPtr"] P.Mload [Expr.Lit 64],
          Stmt.LetPrimCall ["split_expr_5"] P.Shl [Expr.Lit 229, Expr.Lit 4594637],
          Stmt.ExprStmtPrimCall P.Mstore [Expr.Var "memPtr", Expr.Var "split_expr_5"],
          Stmt.LetPrimCall ["split_expr_6"] P.Add [Expr.Var "memPtr", Expr.Lit 4],
          Stmt.ExprStmtPrimCall P.Mstore [Expr.Var "split_expr_6", Expr.Lit 32],
          Stmt.LetPrimCall ["split_expr_7"] P.Add [Expr.Var "memPtr", Expr.Lit 36],
          Stmt.ExprStmtPrimCall P.Mstore [Expr.Var "split_expr_7", Expr.Lit 32],
          Stmt.LetPrimCall ["split_expr_8"] P.Add [Expr.Var "memPtr", Expr.Lit 68],
          Stmt.ExprStmtPrimCall P.Mstore [Expr.Var "split_expr_8", Expr.Lit 0],
          Stmt.ExprStmtPrimCall P.Revert [Expr.Var "memPtr", Expr.Lit 100]])
      = if_7506504477940969768 := rfl

/-- Same fact phrased for an arbitrary `Ok`-shaped state.  The implication
    hypothesis is taken first so that applying it pins down `s` before the
    side conditions are discharged. -/
lemma if_owner_reverted_iff'
    {s : State} {fuel : ℕ}
    (himp : (🧟(exec fuel if_7506504477940969768 s)).evm.reverted = false)
    (hs : s.isOk) (hr : s.evm.reverted = false) :
    s["split_expr_4"]!! ≠ 0 := by
  obtain ⟨evm, store, rfl⟩ := State_of_isOk hs
  exact if_owner_reverted_iff (by simpa [State.evm] using hr) himp

/--
  CLEAN guard theorem for `_checkOwner`.

  If `checkOwner` is run from a fresh (non-reverted) `Ok` state and the resulting
  state `s₉` is itself NON-reverting, then the caller IS the contract owner:

      Fin.land (evm.sload 51) (2^160 - 1)  =  evm.execution_env.source.

  In words: a *successful* `_checkOwner` execution implies the `onlyOwner`
  precondition `owner() == _msgSender()` held.  This "success ⇒ precondition"
  reading was impossible before the `reverted` flag, because a reverting run
  still produced an `Ok` state indistinguishable from success.
-/
theorem fun_checkOwner_clean
    {evm : EVMState} {store : VarStore} {s₉ : State} {fuel : ℕ}
    (hr : evm.reverted = false)
    (hexec : execCall fuel fun_checkOwner [] (Ok evm store, []) = s₉) :
    s₉.evm.reverted = false →
      Fin.land (evm.sload 51) (Fin.shiftLeft 1 160 - 1)
        = (↑↑evm.execution_env.source : UInt256) := by
  intro hno_revert
  -- Unfold the call: with 0 params and 0 rets,
  --   execCall = call's third component = setStore (overwrite? (🧟 s₂) base) base,
  -- where s₂ = exec fuel (Block body) (Ok evm default).
  rw [← hexec] at hno_revert
  unfold execCall call fun_checkOwner at hno_revert
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons] at hno_revert
  -- Replay the 6-statement prelude (sload, shl, sub, and, caller, eq), each a
  -- primop preserving `reverted`, accumulating split_expr_4 = (owner == caller).
  simp only [cons, ExprStmtPrimCall', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMSload', EVMShl', EVMSub', EVMAnd', EVMCaller', EVMEq'] at hno_revert
  -- Strip the trivial wrappers (`multifill [] [] s = s`, `exec (Block []) s = s`)
  -- and convert the post-prelude state to `insert`-over-`Ok` form, reducing the
  -- nested variable lookups so the guard literal `split_expr_4` becomes the clean
  -- boolean `fromBool (decide (owner == caller))`.
  simp only [nil, multifill_nil, multifill_cons, multifill_nil',
             lookup_insert, evm_insert,
             lookup_insert_of_ne (by decide : ("split_expr_0" : Identifier) ≠ "split_expr_1"),
             lookup_insert_of_ne (by decide : ("split_expr_0" : Identifier) ≠ "split_expr_2"),
             lookup_insert_of_ne (by decide : ("split_expr_1" : Identifier) ≠ "split_expr_2"),
             lookup_insert_of_ne (by decide : ("split_expr_0" : Identifier) ≠ "cleaned"),
             lookup_insert_of_ne (by decide : ("split_expr_2" : Identifier) ≠ "cleaned"),
             lookup_insert_of_ne (by decide : ("cleaned" : Identifier) ≠ "split_expr_3")] at hno_revert
  -- Apply the if-block reverted lemma.  Passing `hno_revert` positionally lets
  -- Lean infer the (concrete) post-prelude state `s` first — it is Ok-shaped
  -- (a stack of `insert`s over the Ok base) with the same evm as `evm` (the
  -- prelude only reads) — and the inlined `If` matches `if_7506504477940969768`
  -- definitionally.
  rw [checkOwner_if_eq] at hno_revert
  -- Strip the `call` post-processing wrappers around `s₂`:
  --   s₉ = (🧟 s₂).overwrite? base |>.setStore base,  and base = `Ok evm store`,
  -- so  s₉.evm = (🧟 s₂).evm  (overwrite? is the identity on Ok; setStore keeps evm).
  simp only [overwrite?_of_Ok, evm_setStore] at hno_revert
  -- Apply the if-block reverted lemma; passing `hno_revert` first pins down the
  -- (concrete) post-prelude state, after which the side conditions are routine:
  -- it is Ok-shaped (`insert`s over the Ok base) with evm unchanged from `evm`.
  have hne := if_owner_reverted_iff' (fuel := fuel) hno_revert
      (by simp only [isOk_insert]; apply isOk_initcall_of_isOk; trivial)
      (by simp only [evm_insert]; exact hr)
  -- The guard literal `split_expr_4` IS `fromBool (decide (owner == caller))`.
  rw [lookup_insert' (by simp only [isOk_insert]; apply isOk_initcall_of_isOk; trivial)] at hne
  -- `hne` states `fromBool (decide D) ≠ 0`, where the boolean `D` is the
  -- prelude-computed guard.  `D` is DEFINITIONALLY the clean owner==caller test
  -- `Fin.land (evm.sload 51) (2^160-1) = source`, so the goal follows: if it
  -- failed, `decide D = false`, making `fromBool (decide D) = 0`.
  by_contra hcontra
  apply hne
  show fromBool (decide (Fin.land (evm.sload 51) (Fin.shiftLeft 1 160 - 1)
                        = (↑↑evm.execution_env.source : UInt256))) = 0
  rw [decide_eq_false hcontra]; rfl

end

end generated.L1Bridgehub.L1Bridgehub
