import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_6547236921511043342

import generated.L1Bridgehub.L1Bridgehub.fun_requireNotPaused_gen

import specs.L1Bridgehub.L1Bridgehub.fun_requireNotPaused_user

import specs.RevertModel

/-
  CLEAN guard theorem for `fun_requireNotPaused`
  (OpenZeppelin `Pausable._requireNotPaused()`):
      require(!paused(), "Pausable: paused");
  enabled by the new `reverted` flag on `EVMState`.

  Old form (fun_requireNotPaused_user.lean): the spec could only state that the
  guard literal *computes* the right boolean and that the revert if-block runs,
  because in this EVM model a `revert` still left the state `Ok` — so a
  successful run and a reverting run were indistinguishable by `isOk`.

  New form (here): with the `reverted` flag, a NON-reverting (i.e. genuinely
  successful) execution of `requireNotPaused` IMPLIES the contract is NOT paused:
      Fin.land (evm.sload 151) 255 = 0.
  This is the faithful "success ⇒ precondition held" reading of
      require(!paused()).

  Note the polarity is opposite to `checkOwner`: here the contract reverts when
  the paused bit IS set.  But the *AST shape* of the inlined `if` is identical
  (`if iszero(guard) { …; revert }`, body runs exactly when `guard = 0`), so the
  reverted-iff lemma below has the same structure as `checkOwner`'s.  The guard
  literal is `split_expr_2 = iszero(and(sload 151, 255))`, which is nonzero
  exactly when the paused byte is zero.
-/

namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common Clear.RevertModel

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/--
  Reverted behaviour of the not-paused if-block, proved by direct replay.

  Running `if iszero(split_expr_2) { …; revert(…) }` on `Ok evm store`:
    * if the guard `split_expr_2` is nonzero (paused byte = 0, i.e. NOT paused):
      the body is skipped, the result is the unchanged `Ok evm store`, whose
      `reverted` flag is `evm.reverted`;
    * if the guard is `0` (paused byte ≠ 0, i.e. paused): the body runs and ends
      in `revert`, forcing `reverted = true`.

  Hence, for the output state, `reverted = true` UNLESS the guard was nonzero.
  We state the contrapositive we need: a non-reverting output (given a
  non-reverting input) forces the guard nonzero.
-/
lemma if_paused_reverted_iff
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hr : evm.reverted = false) :
    (🧟(exec fuel if_6547236921511043342 (Ok evm store))).evm.reverted = false →
      (Ok evm store)["split_expr_2"]!! ≠ 0 := by
  unfold if_6547236921511043342
  rw [If']
  -- evaluate the guard `iszero(split_expr_2)`
  simp only [evalArgs, head', reverse', multifill', PrimCall', Lit', Var',
             execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil,
             List.nil_append, List.singleton_append, evalTail, cons']
  rw [EVMIszero']
  simp only [head', List.head!]
  -- case split on whether the guard literal is zero
  by_cases hz : (Ok evm store)["split_expr_2"]!! = 0
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
    intro hbad
    exact absurd hbad (by simp only [Bool.not_eq_false]; rfl)
  · -- guard nonzero ⇒ thesis is exactly `hz`
    intro _
    exact hz

/-- The inlined not-paused `If` statement in `fun_requireNotPaused`'s body is
    exactly the named if-block `if_6547236921511043342` (definitional unfolding). -/
lemma requireNotPaused_if_eq :
    (Stmt.If (Expr.PrimCall P.Iszero [Expr.Var "split_expr_2"])
        [Stmt.LetPrimCall ["memPtr"] P.Mload [Expr.Lit 64],
          Stmt.LetPrimCall ["split_expr_3"] P.Shl [Expr.Lit 229, Expr.Lit 4594637],
          Stmt.ExprStmtPrimCall P.Mstore [Expr.Var "memPtr", Expr.Var "split_expr_3"],
          Stmt.LetPrimCall ["split_expr_4"] P.Add [Expr.Var "memPtr", Expr.Lit 4],
          Stmt.ExprStmtPrimCall P.Mstore [Expr.Var "split_expr_4", Expr.Lit 32],
          Stmt.LetPrimCall ["split_expr_5"] P.Add [Expr.Var "memPtr", Expr.Lit 36],
          Stmt.ExprStmtPrimCall P.Mstore [Expr.Var "split_expr_5", Expr.Lit 16],
          Stmt.LetPrimCall ["split_expr_6"] P.Add [Expr.Var "memPtr", Expr.Lit 68],
          Stmt.ExprStmtPrimCall P.Mstore [Expr.Var "split_expr_6", Expr.Lit 0],
          Stmt.ExprStmtPrimCall P.Revert [Expr.Var "memPtr", Expr.Lit 100]])
      = if_6547236921511043342 := rfl

/-- Same fact phrased for an arbitrary `Ok`-shaped state.  The implication
    hypothesis is taken first so that applying it pins down `s` before the
    side conditions are discharged. -/
lemma if_paused_reverted_iff'
    {s : State} {fuel : ℕ}
    (himp : (🧟(exec fuel if_6547236921511043342 s)).evm.reverted = false)
    (hs : s.isOk) (hr : s.evm.reverted = false) :
    s["split_expr_2"]!! ≠ 0 := by
  obtain ⟨evm, store, rfl⟩ := State_of_isOk hs
  exact if_paused_reverted_iff (by simpa [State.evm] using hr) himp

/--
  CLEAN guard theorem for `_requireNotPaused`.

  If `requireNotPaused` is run from a fresh (non-reverted) `Ok` state and the
  resulting state `s₉` is itself NON-reverting, then the contract is NOT paused:

      Fin.land (evm.sload 151) 255  =  0.

  In words: a *successful* `_requireNotPaused` execution implies the
  `whenNotPaused` precondition `!paused()` held.  This "success ⇒ precondition"
  reading was impossible before the `reverted` flag, because a reverting run
  still produced an `Ok` state indistinguishable from success.
-/
theorem fun_requireNotPaused_clean
    {evm : EVMState} {store : VarStore} {s₉ : State} {fuel : ℕ}
    (hr : evm.reverted = false)
    (hexec : execCall fuel fun_requireNotPaused [] (Ok evm store, []) = s₉) :
    s₉.evm.reverted = false →
      Fin.land (evm.sload 151) 255 = 0 := by
  intro hno_revert
  -- Unfold the call: with 0 params and 0 rets,
  --   execCall = setStore (overwrite? (🧟 s₂) base) base,
  -- where s₂ = exec fuel (Block body) (Ok evm default).
  rw [← hexec] at hno_revert
  unfold execCall call fun_requireNotPaused at hno_revert
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons] at hno_revert
  -- Replay the 3-statement prelude (sload, and, iszero), each a primop
  -- preserving `reverted`, accumulating split_expr_2 = iszero(and(sload 151,255)).
  simp only [cons, ExprStmtPrimCall', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMSload', EVMAnd', EVMIszero'] at hno_revert
  -- Strip the trivial wrappers and convert the post-prelude state to `insert`-over-`Ok`
  -- form, reducing nested variable lookups.
  simp only [nil, multifill_nil, multifill_cons, multifill_nil',
             lookup_insert, evm_insert,
             lookup_insert_of_ne (by decide : ("split_expr_0" : Identifier) ≠ "split_expr_1")] at hno_revert
  -- Fold the inlined `If` to the named if-block.
  rw [requireNotPaused_if_eq] at hno_revert
  -- Strip the `call` post-processing wrappers around `s₂`.
  simp only [overwrite?_of_Ok, evm_setStore] at hno_revert
  -- Apply the if-block reverted lemma; passing `hno_revert` first pins down the
  -- (concrete) post-prelude state, after which the side conditions are routine:
  -- it is Ok-shaped (`insert`s over the Ok base) with evm unchanged from `evm`.
  have hne := if_paused_reverted_iff' (fuel := fuel) hno_revert
      (by simp only [isOk_insert]; apply isOk_initcall_of_isOk; trivial)
      (by simp only [evm_insert]; exact hr)
  -- The guard literal `split_expr_2` IS `fromBool (decide (paused byte = 0))`.
  rw [lookup_insert' (by simp only [isOk_insert]; apply isOk_initcall_of_isOk; trivial)] at hne
  -- `hne` states `fromBool (decide D) ≠ 0`, where the boolean `D` is the
  -- prelude-computed guard `Fin.land (evm.sload 151) 255 = 0`.  Hence the goal:
  -- if it failed, `decide D = false`, making `fromBool (decide D) = 0`.
  by_contra hcontra
  apply hne
  show fromBool (decide (Fin.land (evm.sload 151) 255 = 0)) = 0
  rw [decide_eq_false hcontra]; rfl

end

end generated.L1Bridgehub.L1Bridgehub
