import Clear.ReasoningPrinciple

import specs.KeccakDeterminism

/-
  THE EXECUTOR BINDING (L2InteropHandler, post-relocation corpus).

  Upstream PR #2303 moved InteropHandler into `interop-handler/` and the new
  compile INLINES `requireExecutionAllowed` into the dispatcher's
  `executeBundle` branch (src 43:5456:5603 of InteropHandlerBase.sol).  The
  authorization computation is source-identical to the old corpus but the
  optimized IR folds the caller/address reads and the 160-bit mask into
  nested expressions:

      let expr_8 := eq(caller(), address())
      if iszero(expr_8) {
          let expr_9 := eq(expr_component_15, chainid())
          if iszero(expr_9) { expr_9 := iszero(expr_component_15) }
          let expr_10 := expr_9
          if expr_9 {
              expr_10 := eq(and(expr_component_16, sub(shl(160, 1), 1)), caller())
          }
          expr_8 := expr_10
      }

  This file proves the PASS directions over that verbatim block:

  * `auth_self_pass`      — the handler's own call is authorized;
  * `auth_executor_pass`  — the designated executor on the right chain is
    authorized (both the exact-chain and chain-agnostic forms);

  the port of the old-corpus `exec_allowed_user` theorems, same named-sub-if
  drive.  Axiom-free.
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

/-! ### The authorization block, quoted verbatim -/

/-- The inlined authorization computation of `executeBundle`. -/
private def authBlk : Stmt := <s
  {
    let expr_8 := eq(caller(), address())
    if iszero(expr_8)
    {
        let expr_9 := eq(expr_component_15, chainid())
        if iszero(expr_9)
        {
            expr_9 := iszero(expr_component_15)
        }
        let expr_10 := expr_9
        if expr_9
        {
            expr_10 := eq(and(expr_component_16, sub(shl(160, 1), 1)), caller())
        }
        expr_8 := expr_10
    }
}
>

/-- The chain-fallback if: on an inexact chain match, accept iff the declared
chain is `0` (chain-agnostic). -/
@[reducible] private def chainIf : Stmt := <s
  if iszero(expr_9)
  {
      expr_9 := iszero(expr_component_15)
  }
>

/-- The mask-and-compare if: mask the declared address to 160 bits, compare
with the caller — all in one nested expression in this corpus. -/
@[reducible] private def maskIf : Stmt := <s
  if expr_9
  {
      expr_10 := eq(and(expr_component_16, sub(shl(160, 1), 1)), caller())
  }
>

/-- `chainIf` on an exact chain match (`expr_9 = 1`): the guard `iszero` fails,
the store is untouched. -/
private theorem chainIf_skip
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    (h1 : (Ok evm σ)["expr_9"]!! = 1) :
    exec fuel chainIf (Ok evm σ) = Ok evm σ := by
  unfold chainIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [h1]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  simp only [List.head!]
  rw [if_neg (by exact fun h => h rfl)]

/-- `chainIf` on an inexact match with a chain-agnostic declaration
(`expr_9 = 0`, declared chain `= 0`): the branch runs and flips `expr_9` to 1. -/
private theorem chainIf_agnostic
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    (h1 : (Ok evm σ)["expr_9"]!! = 0)
    (hC : (Ok evm σ)["expr_component_15"]!! = 0) :
    exec fuel chainIf (Ok evm σ) = Ok evm (σ.insert "expr_9" 1) := by
  unfold chainIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [h1]
  rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  simp only [List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  simp only [cons, nil]
  rw [AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMIszero']
  rw [hC]
  rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  rw [insert_Ok]

/-- `maskIf` with the authorization granted on the chain side (`expr_9 = 1`)
and the masked declared address equal to the caller: the single nested-eq
assignment sets `expr_10 = 1`. -/
private theorem maskIf_pass
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {A : Literal}
    (h1 : (Ok evm σ)["expr_9"]!! = 1)
    (hA : (Ok evm σ)["expr_component_16"]!! = A)
    (hmask : Fin.land A (Fin.shiftLeft 1 160 - 1)
        = ((evm.execution_env.source : UInt256))) :
    exec fuel maskIf (Ok evm σ) = Ok evm (σ.insert "expr_10" 1) := by
  unfold maskIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append]
  rw [h1]
  try simp only [List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  simp only [cons, nil]
  rw [AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil,
             EVMEq', EVMAnd', EVMSub', EVMShl', EVMCaller', evm_Ok]
  simp only [List.head!]
  rw [hA]
  simp only [decide_eq_true hmask]
  rw [show fromBool true = (1 : UInt256) from by decide]
  rw [insert_Ok]

/-- **SELF-CALL PASSES**: when the caller IS the handler, the authorization
value `expr_8` computes to `1` with the evm unchanged. -/
theorem auth_self_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hself : ((evm.execution_env.source : UInt256))
        = ((evm.execution_env.code_owner : UInt256))) :
    ∃ σ' : VarStore,
      exec (fuel+1) authBlk (Ok evm store) = Ok evm σ'
      ∧ (Ok evm σ')["expr_8"]!! = 1 := by
  unfold authBlk
  -- let expr_8 := eq(caller(), address())
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMCaller', EVMAddress', EVMEq', evm_Ok, insert_Ok]
  simp only [List.head!]
  rw [show fromBool (((evm.execution_env.source : UInt256))
      = ((evm.execution_env.code_owner : UInt256)))
      = (1 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_true hself, if_true]]
  -- outer if: iszero(expr_8) with expr_8 = 1 — skip
  rw [cons, nil, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  try simp only [lookup_insert_self_fin]
  try rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  refine ⟨_, rfl, ?_⟩
  exact lookup_insert_self_fin

/-- **THE DESIGNATED EXECUTOR PASSES** (new corpus): when the caller is NOT
the handler but the bundle's parsed executor matches — the declared chain is
the current chain or the chain-agnostic `0`, and the 160-bit-masked declared
address equals the caller — the authorization value `expr_8` computes to `1`
with the evm unchanged.  Port of the old-corpus theorem to the inlined block. -/
theorem auth_executor_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {C A : Literal}
    (hC : (Ok evm store)["expr_component_15"]!! = C)
    (hA : (Ok evm store)["expr_component_16"]!! = A)
    (hne : ((evm.execution_env.source : UInt256))
        ≠ ((evm.execution_env.code_owner : UInt256)))
    (hchain : C = evm.chainId ∨ C = 0)
    (hmask : Fin.land A (Fin.shiftLeft 1 160 - 1)
        = ((evm.execution_env.source : UInt256))) :
    ∃ σ' : VarStore,
      exec (fuel+1) authBlk (Ok evm store) = Ok evm σ'
      ∧ (Ok evm σ')["expr_8"]!! = 1 := by
  unfold authBlk
  -- let expr_8 := eq(caller(), address())
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMCaller', EVMAddress', EVMEq', evm_Ok, insert_Ok]
  simp only [List.head!]
  rw [show fromBool (((evm.execution_env.source : UInt256))
      = ((evm.execution_env.code_owner : UInt256)))
      = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hne, if_false]]
  -- outer if: iszero(expr_8) with expr_8 = 0 — enter
  rw [cons, nil, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  try simp only [lookup_insert_self_fin]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_pos (by decide : fromBool (decide True) ≠ (0 : UInt256))]
  -- let expr_9 := eq(expr_component_15, chainid())
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMChainid', EVMEq', evm_Ok, insert_Ok]
  try simp only [List.head!]
  rw [lookup_insert_ne_fin (by decide), hC]
  -- split on the chain-match shape
  by_cases hcid : C = evm.chainId
  · -- exact chain match: expr_9 = 1, chainIf skips
    rw [show fromBool (C = evm.chainId) = (1 : UInt256) from by
      simp only [fromBool, Bool.toUInt256, decide_eq_true hcid, if_true]]
    rw [cons]
    rw [chainIf_skip lookup_insert_self_fin]
    -- let expr_10 := expr_9
    rw [cons, LetEq']
    simp only [Var', insert_Ok]
    rw [lookup_insert_self_fin]
    -- the mask if
    rw [cons]
    rw [maskIf_pass
      (by rw [lookup_insert_ne_fin (by decide)]; exact lookup_insert_self_fin)
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide)]
          exact hA)
      hmask]
    -- expr_8 := expr_10
    rw [cons, nil, Assign']
    simp only [Var', insert_Ok]
    rw [lookup_insert_self_fin]
    refine ⟨_, rfl, ?_⟩
    exact lookup_insert_self_fin
  · -- inexact chain: the declaration must be the chain-agnostic 0
    have hc0 : C = 0 := by
      rcases hchain with h | h
      · exact absurd h hcid
      · exact h
    rw [show fromBool (C = evm.chainId) = (0 : UInt256) from by
      simp only [fromBool, Bool.toUInt256, decide_eq_false hcid, if_false]]
    rw [cons]
    rw [chainIf_agnostic lookup_insert_self_fin
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          rw [hC]; exact hc0)]
    -- let expr_10 := expr_9
    rw [cons, LetEq']
    simp only [Var', insert_Ok]
    rw [lookup_insert_self_fin]
    -- the mask if
    rw [cons]
    rw [maskIf_pass
      (by rw [lookup_insert_ne_fin (by decide)]; exact lookup_insert_self_fin)
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact hA)
      hmask]
    -- expr_8 := expr_10
    rw [cons, nil, Assign']
    simp only [Var', insert_Ok]
    rw [lookup_insert_self_fin]
    refine ⟨_, rfl, ?_⟩
    exact lookup_insert_self_fin

end

end generated.L2InteropHandler.L2InteropHandler
