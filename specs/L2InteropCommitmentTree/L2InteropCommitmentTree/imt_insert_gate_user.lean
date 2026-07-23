import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.constant_L2_ATOMIC_FLOW_MANAGER_ADDR

/-
  THE INSERT GATES (L2InteropCommitmentTree dispatcher glue).

  The `insert` entry (source-verbatim (B) boundary, yul 140-262) guards:

  * the APPENDER GATE — `msg.sender` must be the 160-bit-masked
    `L2_ATOMIC_FLOW_MANAGER_ADDR` built-in (`0x10014`), else
    `CommitmentTreeNotAppender`: only the AtomicFlowManager can grow the
    commitment tree;
  * the DEDUP GATE — `valueToIndex[_value] == 0`, else
    `IMTValueAlreadyExists`: the concrete exactly-once enforcement
    (abstract side: `evolution_insert_unique`, #46, and the strictness
    upgrade `window_strict_of_not_mem`).

  The glue is UNSPLIT Yul (calls in expression position), so the condition
  drives go through `Call'`/`evalCall` with call-level closed forms.  This
  file starts the ladder: the constant loader.

  Axiom-free.
-/

namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.dupNamespace false

@[simp] private lemma insert_Ok {evm : EVMState} {store : VarStore}
    {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

/-- **The appender constant, call level**: `constant_L2_ATOMIC_FLOW_MANAGER_ADDR()`
returns the AFM built-in `65556 = 0x10014` and leaves the caller state
untouched.  Call-level (the pair), so it feeds `evalCall` for the
in-expression occurrence in the appender gate. -/
lemma constant_afm_call {evm : EVMState} {σ : VarStore} {fuel : ℕ} :
    call (fuel+1) [] constant_L2_ATOMIC_FLOW_MANAGER_ADDR (Ok evm σ)
      = (Ok evm σ, [(65556 : Literal)]) := by
  unfold call constant_L2_ATOMIC_FLOW_MANAGER_ADDR
  simp only [params, body, rets, mkOk_initcall_Ok, List.map_nil, List.map_cons]
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  rw [cons, Assign']
  simp only [Lit', insert_Ok]
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  rw [cons, Assign']
  simp only [Lit', insert_Ok]
  rw [cons, nil, Assign']
  simp only [Var', Lit', insert_Ok]
  rfl

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
