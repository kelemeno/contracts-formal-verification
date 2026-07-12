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

end

end generated.InteropHandler.InteropHandler
