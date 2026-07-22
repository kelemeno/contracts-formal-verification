import Clear.ReasoningPrinciple

import specs.KeccakDeterminism

/-
  THE EXECUTOR BINDING — who may trigger a delivery.

  `fun_requireExecutionAllowed` restricts bundle execution when the bundle
  carries a nonempty `executionAddress`: the caller must be the handler
  itself (internal receive-and-execute), or the DESIGNATED executor — the
  parsed `(chainId, address)` must match the current chain (or be
  chain-agnostic, `chainId = 0`) and the masked address must equal the
  caller.  This file proves the PASS directions of the authorization
  computation over its verbatim compiled block:

  * `auth_self_pass`      — the handler's own call is authorized;
  * `auth_executor_pass`  — the designated executor on the right chain is
    authorized (both the exact-chain and chain-agnostic forms);

  so a delivery can be triggered by exactly the parties the bundle names —
  spec point 2's intended-executor binding.  (The revert direction of the
  final gate awaits the dynamic error-encoder's closed form, as in #37.)

  Axiom-free.
-/

namespace generated.InteropHandler.InteropHandler

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

/-- The authorization computation: self-call, or (right chain ∨ any-chain)
and the masked designated address equals the caller. -/
private def authBlk : Stmt := <s
  {
    let split_expr_2 := caller()
    let split_expr_3 := address()
    let expr := eq(split_expr_2, split_expr_3)
    if iszero(expr)
    {
        let split_expr_4 := chainid()
        let expr_1 := eq(expr_287_component, split_expr_4)
        if iszero(expr_1)
        {expr_1 := iszero(expr_287_component)}
        let expr_2 := expr_1
        if expr_1
        {
            let split_expr_5 := shl(160, 1)
            let split_expr_6 := sub(split_expr_5, 1)
            let split_expr_7 := and(expr_component, split_expr_6)
            let split_expr_8 := caller()
            expr_2 := eq(split_expr_7, split_expr_8)
        }
        expr := expr_2
    }
}
>

/-- **SELF-CALL PASSES**: when the caller IS the handler, the authorization
value `expr` computes to `1` with the evm unchanged. -/
theorem auth_self_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hself : ((evm.execution_env.source : UInt256))
        = ((evm.execution_env.code_owner : UInt256))) :
    ∃ σ' : VarStore,
      exec (fuel+1) authBlk (Ok evm store) = Ok evm σ'
      ∧ (Ok evm σ')["expr"]!! = 1 := by
  unfold authBlk
  simp only [cons, nil]
  simp only [If', LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMCaller', EVMAddress', EVMEq', EVMIszero']
  simp only [multifill_cons, multifill_nil]
  simp only [evm_insert, evm_Ok, setEvm_Ok, insert_Ok]
  try simp only [lookup_insert_self_fin]
  have n1 : (Ok evm (Finmap.insert "split_expr_3"
      ((evm.execution_env.code_owner : UInt256))
      (Finmap.insert "split_expr_2"
        ((evm.execution_env.source : UInt256)) store)))["split_expr_2"]!!
      = ((evm.execution_env.source : UInt256)) := by
    rw [lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  simp only [n1]
  simp only [show fromBool (((evm.execution_env.source : UInt256))
      = ((evm.execution_env.code_owner : UInt256)))
      = (1 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_true hself, if_true]]
  try simp only [lookup_insert_self_fin]
  try simp only [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try rw [if_neg (by exact fun h => h rfl)]
  refine ⟨_, rfl, ?_⟩
  try simp only [lookup_insert_self_fin]
  try rw [lookup_insert_self_fin]

/-! ### The designated-executor pass — nested-if drive via named sub-statements

The other accepting case — caller is not the handler, but the parsed
`(chainId, address)` matches the current chain (or is chain-agnostic `0`) and
the masked address equals the caller — is a nested-if dataflow with an
assignment inside a branch.  A monolithic `If'`-blast distributes the trailing
`expr := expr_2` over the unresolved inner `if expr_1`; instead the two nested
ifs are quoted as NAMED sub-statements and closed by standalone generic-σ
lemmas, which the main drive rewrites in one at a time once the store tower
below each is closed. -/

/-- The chain-fallback if: on an inexact chain match, accept iff the declared
chain is `0` (chain-agnostic). -/
@[reducible] private def chainIf : Stmt := <s
  if iszero(expr_1)
  {expr_1 := iszero(expr_287_component)}
>

/-- The mask-and-compare if: mask the declared address to 160 bits and compare
with the caller. -/
@[reducible] private def maskIf : Stmt := <s
  if expr_1
  {
      let split_expr_5 := shl(160, 1)
      let split_expr_6 := sub(split_expr_5, 1)
      let split_expr_7 := and(expr_component, split_expr_6)
      let split_expr_8 := caller()
      expr_2 := eq(split_expr_7, split_expr_8)
  }
>

/-- `chainIf` on an exact chain match (`expr_1 = 1`): the guard `iszero` fails,
the store is untouched. -/
private theorem chainIf_skip
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    (h1 : (Ok evm σ)["expr_1"]!! = 1) :
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
(`expr_1 = 0`, declared chain `= 0`): the branch runs and flips `expr_1` to 1. -/
private theorem chainIf_agnostic
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    (h1 : (Ok evm σ)["expr_1"]!! = 0)
    (hC : (Ok evm σ)["expr_287_component"]!! = 0) :
    exec fuel chainIf (Ok evm σ) = Ok evm (σ.insert "expr_1" 1) := by
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

/-- `maskIf` with the authorization already granted on the chain side
(`expr_1 = 1`) and the masked declared address equal to the caller: the branch
runs and re-affirms `expr_2 = 1`.  The conclusion pins the full insert tower so
the caller's drive stays closed. -/
private theorem maskIf_pass
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {A : Literal}
    (h1 : (Ok evm σ)["expr_1"]!! = 1)
    (hA : (Ok evm σ)["expr_component"]!! = A)
    (hmask : Fin.land A (Fin.shiftLeft 1 160 - 1)
        = ((evm.execution_env.source : UInt256))) :
    exec fuel maskIf (Ok evm σ)
      = Ok evm (((((σ.insert "split_expr_5" (Fin.shiftLeft 1 160)).insert
          "split_expr_6" (Fin.shiftLeft 1 160 - 1)).insert
          "split_expr_7" (Fin.land A (Fin.shiftLeft 1 160 - 1))).insert
          "split_expr_8" ((evm.execution_env.source : UInt256))).insert
          "expr_2" 1) := by
  unfold maskIf
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append]
  rw [h1]
  try simp only [List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- let split_expr_5 := shl(160, 1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- let split_expr_6 := sub(split_expr_5, 1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMSub',
             insert_Ok]
  rw [lookup_insert_self_fin]
  -- let split_expr_7 := and(expr_component, split_expr_6)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAnd',
             insert_Ok]
  rw [lookup_insert_self_fin,
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hA]
  -- let split_expr_8 := caller()
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMCaller',
             evm_Ok, insert_Ok]
  -- expr_2 := eq(split_expr_7, split_expr_8)
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMEq',
             insert_Ok]
  rw [lookup_insert_self_fin,
      lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [hmask]
  rw [show fromBool (((evm.execution_env.source : UInt256))
      = ((evm.execution_env.source : UInt256))) = (1 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_true rfl, if_true]
    decide]

/-- **THE DESIGNATED EXECUTOR PASSES**: when the caller is NOT the handler but
the bundle's parsed executor matches — the declared chain is the current chain
or the chain-agnostic `0`, and the 160-bit-masked declared address equals the
caller — the authorization value `expr` computes to `1` with the evm
unchanged.  Together with `auth_self_pass` this is the complete accepting
surface of spec point 2's intended-executor binding. -/
theorem auth_executor_pass
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {C A : Literal}
    (hC : (Ok evm store)["expr_287_component"]!! = C)
    (hA : (Ok evm store)["expr_component"]!! = A)
    (hne : ((evm.execution_env.source : UInt256))
        ≠ ((evm.execution_env.code_owner : UInt256)))
    (hchain : C = evm.chainId ∨ C = 0)
    (hmask : Fin.land A (Fin.shiftLeft 1 160 - 1)
        = ((evm.execution_env.source : UInt256))) :
    ∃ σ' : VarStore,
      exec (fuel+1) authBlk (Ok evm store) = Ok evm σ'
      ∧ (Ok evm σ')["expr"]!! = 1 := by
  unfold authBlk
  simp only [cons, nil]
  -- the three prefix lets and the outer guard `eq(caller, address)` = 0
  simp only [LetPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMCaller', EVMAddress', EVMEq']
  simp only [evm_insert, evm_Ok, setEvm_Ok, insert_Ok]
  try simp only [lookup_insert_self_fin]
  have n1 : (Ok evm (Finmap.insert "split_expr_3"
      ((evm.execution_env.code_owner : UInt256))
      (Finmap.insert "split_expr_2"
        ((evm.execution_env.source : UInt256)) store)))["split_expr_2"]!!
      = ((evm.execution_env.source : UInt256)) := by
    rw [lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  simp only [n1]
  simp only [show fromBool (((evm.execution_env.source : UInt256))
      = ((evm.execution_env.code_owner : UInt256)))
      = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hne, if_false]]
  -- outer if: iszero(expr) with expr = 0 — enter the body
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  try simp only [lookup_insert_self_fin]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_pos (by decide : fromBool (decide True) ≠ (0 : UInt256))]
  -- let split_expr_4 := chainid()
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMChainid', evm_Ok, insert_Ok]
  -- let expr_1 := eq(expr_287_component, split_expr_4)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMEq',
             insert_Ok]
  rw [lookup_insert_self_fin,
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hC]
  -- split on the chain-match shape
  by_cases hcid : C = evm.chainId
  · -- exact chain match: expr_1 = 1, chainIf skips
    rw [show fromBool (C = evm.chainId) = (1 : UInt256) from by
      simp only [fromBool, Bool.toUInt256, decide_eq_true hcid, if_true]]
    rw [cons]
    rw [chainIf_skip lookup_insert_self_fin]
    -- let expr_2 := expr_1
    rw [cons, LetEq']
    simp only [Var', insert_Ok]
    rw [lookup_insert_self_fin]
    -- the mask if
    rw [cons]
    rw [maskIf_pass
      (by rw [lookup_insert_ne_fin (by decide)]; exact lookup_insert_self_fin)
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact hA)
      hmask]
    -- expr := expr_2
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
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide)]
          rw [hC]; exact hc0)]
    -- let expr_2 := expr_1
    rw [cons, LetEq']
    simp only [Var', insert_Ok]
    rw [lookup_insert_self_fin]
    -- the mask if
    rw [cons]
    rw [maskIf_pass
      (by rw [lookup_insert_ne_fin (by decide)]; exact lookup_insert_self_fin)
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide)]
          exact hA)
      hmask]
    -- expr := expr_2
    rw [cons, nil, Assign']
    simp only [Var', insert_Ok]
    rw [lookup_insert_self_fin]
    refine ⟨_, rfl, ?_⟩
    exact lookup_insert_self_fin

end

end generated.InteropHandler.InteropHandler
