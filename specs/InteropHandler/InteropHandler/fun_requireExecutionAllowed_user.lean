import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_8834218201084202482
import generated.InteropHandler.InteropHandler.fun_parseEvmV1
import generated.InteropHandler.InteropHandler.Common.if_634637932385186807
import generated.InteropHandler.InteropHandler.fun_formatEvmV1
import generated.InteropHandler.InteropHandler.Common.if_8907015681698142673
import generated.InteropHandler.InteropHandler.abi_encode_bytes32_bytes_bytes

import generated.InteropHandler.InteropHandler.fun_requireExecutionAllowed_gen


/-
  Abstract spec for the Yul translation of InteropHandler's
  `_requireExecutionAllowed(bundleHash, interopBundle)` — the EXECUTOR
  AUTHORIZATION gate: who may trigger delivery of an interop bundle.

  Solidity semantics (cf. the compiled Yul in
  fun_requireExecutionAllowed_gen.lean and the deep pass-direction proofs in
  specs/InteropHandler/InteropHandler/exec_allowed_user.lean):

    * load the bundle's `executionAddress` field (`bytes`, at struct offset
      192): if it is EMPTY (length 0) the bundle is unrestricted — leave,
      execution allowed for anyone;
    * otherwise parse it as EvmV1 into (chainId, address) and authorize iff
        caller == address(this)                       (self receive-and-execute)
      OR ((chainId == block.chainid ∨ chainId == 0)   (right chain / any chain)
          ∧ (address & (2^160-1)) == caller);         (designated executor)
    * if not authorized, revert with an error carrying
      (bundleHash, formatEvmV1(block.chainid, caller), executionAddress).

  WHAT THIS ABSTRACT SPEC PINS (and what it does not).  The sub-blocks of this
  function (the leave-gate, the authorization block, the revert-gate) and the
  callees (parseEvmV1, formatEvmV1) have their own abstract specs
  (`A_if_...`, `A_fun_parseEvmV1`, `A_fun_formatEvmV1`) which are still stubs,
  so — exactly as in the completed fun_validateChainParams spec for
  L1Bridgehub — this spec characterizes the function as the IN-ORDER ROUTING
  through those named sub-blocks, pinning every value the surrounding
  straight-line code computes, in closed form:

    1. the leave-gate (empty-executionAddress check) is entered from the
       UNTOUCHED caller state (evm unchanged; fresh varstore holding only the
       two arguments) extended with the genuine field dataflow
           _1           = interopBundle + 192
           split_expr_0 = mload(interopBundle + 192)       -- ptr to executionAddress
           _2           = mload(mload(interopBundle + 192)) -- its data cell
           split_expr_1 = mload(_2)                          -- guard the gate tests
       i.e. the gate's guard is exactly the bundle's executionAddress content
       word — the "is the bundle execution-restricted?" test;
    2. parseEvmV1 is invoked on `_2` — the executionAddress payload — and its
       two results are bound to (expr_287_component, expr_component)
       = (declared chainId, declared executor address);
    3. the executor-authorization block is entered with
           split_expr_2 = caller()  (= evm.execution_env.source)
           split_expr_3 = address() (= evm.execution_env.code_owner)
           expr         = fromBool (caller == address(this))
       — the SELF-CALL flag is pinned to the genuine comparison; the deep
       accepting-direction semantics of the block itself are proved in
       exec_allowed_user.lean (auth_self_pass / auth_executor_pass);
    4. formatEvmV1 is invoked on (block.chainid, caller()) — the canonical
       encoding of the actual sender used in the revert payload;
    5. the revert-gate is entered with the executionAddress reloaded
       (split_expr_11 = mload(_1), _3 = mload(split_expr_11)) for the error
       payload;
    6. FRAME: the final state is the revived output of the revert-gate merged
       back onto the caller's varstore — locals do not leak, and the caller's
       variable store is untouched.

  NOT captured here (honestly): the input/output behaviour INSIDE the five
  abstracted sub-parts — those are the `A_if_.../A_fun_...` stubs, to be
  strengthened in their own files; once they are, this routing spec composes
  them without change.  In this EVM model a `revert` still yields an `Ok`
  state, so no isOk-based success/failure distinction is possible at this
  level (same caveat as fun_validateChainParams / bridgehub_caller_guard).
-/

namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option linter.dupNamespace false

/-! ### Local state-plumbing helpers (same as exec_allowed_user.lean) -/

@[simp] private lemma insert_Ok' {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

@[simp] private lemma evm_Ok' {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

private lemma lookup_insert_self_fin' {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok']; exact lookup_insert' (by trivial)

private lemma lookup_insert_ne_fin' {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok']; exact lookup_insert_of_ne h

/-! ### The pinned intermediate states of the routing chain -/

/-- Entry state of the leave-gate (`if iszero(split_expr_1) {leave}`): the
untouched caller evm, a fresh varstore with the two arguments, and the genuine
executionAddress dataflow of the bundle struct:
`_1 = &bundle.executionAddress`, `split_expr_0 = mload _1` (the bytes pointer),
`_2 = mload split_expr_0`, and the gate's guard
`split_expr_1 = mload _2` — the executionAddress content word whose zeroness
means "bundle unrestricted, execution allowed for anyone". -/
def A_requireExecutionAllowed_entry
    (evm : EVM) (var_bundleHash var__interopBundle_mpos : Literal) : State :=
  Ok evm
    (Finmap.insert "split_expr_1"
      (EVMState.mload evm (EVMState.mload evm (EVMState.mload evm (var__interopBundle_mpos + 192))))
    (Finmap.insert "_2"
      (EVMState.mload evm (EVMState.mload evm (var__interopBundle_mpos + 192)))
    (Finmap.insert "split_expr_0"
      (EVMState.mload evm (var__interopBundle_mpos + 192))
    (Finmap.insert "_1" (var__interopBundle_mpos + 192)
    (Finmap.insert "var_bundleHash" var_bundleHash
    (Finmap.insert "var__interopBundle_mpos" var__interopBundle_mpos
      Inhabited.default))))))

/-- Entry state of the executor-authorization block, from the parseEvmV1
output state `s`: binds `split_expr_2 = caller()`, `split_expr_3 = address(this)`
and pins the SELF-CALL flag `expr = fromBool (caller == address(this))`. -/
def A_requireExecutionAllowed_selfCallFlag (s : State) : State :=
  let s₁ := match s with
    | .Ok evm store =>
      Ok evm (Finmap.insert "split_expr_2" ((s.evm.execution_env.source : UInt256)) store)
    | s => s
  let s₂ := match s₁ with
    | .Ok evm store =>
      Ok evm (Finmap.insert "split_expr_3" ((s.evm.execution_env.code_owner : UInt256)) store)
    | s => s
  match s₂ with
  | .Ok evm store =>
    Ok evm (Finmap.insert "expr"
      (fromBool (s₂["split_expr_2"]!! = s₂["split_expr_3"]!!)) store)
  | s => s

/-- Entry state of the formatEvmV1 call, from the authorization-block output
state `s`: binds `split_expr_9 = block.chainid` and `split_expr_10 = caller()`
— the canonical (chain, sender) pair encoded into the revert payload. -/
def A_requireExecutionAllowed_canonicalSender_pre (s : State) : State :=
  let s₁ := match s with
    | .Ok evm store =>
      Ok evm (Finmap.insert "split_expr_9" (EVMState.chainId s.evm) store)
    | s => s
  match s₁ with
  | .Ok evm store =>
    Ok evm (Finmap.insert "split_expr_10" ((s.evm.execution_env.source : UInt256)) store)
  | s => s

/-- Entry state of the revert-gate (`if iszero(expr) { ...revert... }`), from
the formatEvmV1 output state `s`: reloads the bundle's executionAddress for the
error payload — `split_expr_11 = mload _1`, `_3 = mload split_expr_11`. -/
def A_requireExecutionAllowed_revertGate_pre (s : State) : State :=
  let s₁ := match s with
    | .Ok evm store =>
      Ok evm (Finmap.insert "split_expr_11" (EVMState.mload s.evm (s["_1"]!!)) store)
    | s => s
  match s₁ with
  | .Ok evm store =>
    Ok evm (Finmap.insert "_3" (EVMState.mload s.evm (s₁["split_expr_11"]!!)) store)
  | s => s

/-- **The executor-authorization routing spec** (see file header): a run of
`fun_requireExecutionAllowed(bundleHash, interopBundle)` from `Ok evm store`
is exactly the in-order pass through
leave-gate → parseEvmV1 → authorization block → formatEvmV1 → revert-gate,
with every straight-line value pinned to its genuine semantic quantity
(executionAddress dataflow, self-call flag, canonical sender, revert payload
operands), and the final state is the revived revert-gate output merged back
onto the CALLER's untouched varstore (locals frame). -/
def A_fun_requireExecutionAllowed  (var_bundleHash var__interopBundle_mpos : Literal) (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    -- 1. leave-gate: empty executionAddress ⇒ unrestricted bundle, leave.
    ∃ s₁, Spec A_if_8834218201084202482
            (A_requireExecutionAllowed_entry evm var_bundleHash var__interopBundle_mpos) s₁ ∧
    -- 2. parseEvmV1 on the executionAddress payload `_2`
    --    ⇒ (expr_287_component, expr_component) = (declared chainId, declared executor).
    ∃ s₂, Spec (A_fun_parseEvmV1 "expr_287_component" "expr_component" (s₁["_2"]!!)) s₁ s₂ ∧
    -- 3. executor-authorization block, entered with the self-call flag pinned.
    ∃ s₃, Spec A_if_634637932385186807 (A_requireExecutionAllowed_selfCallFlag s₂) s₃ ∧
    -- 4. formatEvmV1(block.chainid, caller()) — canonical actual-sender encoding.
    ∃ s₄, Spec (A_fun_formatEvmV1 "expr_mpos"
            ((A_requireExecutionAllowed_canonicalSender_pre s₃)["split_expr_9"]!!)
            ((A_requireExecutionAllowed_canonicalSender_pre s₃)["split_expr_10"]!!))
            (A_requireExecutionAllowed_canonicalSender_pre s₃) s₄ ∧
    -- 5. revert-gate, entered with the error-payload operands pinned.
    ∃ s₅, Spec A_if_8907015681698142673 (A_requireExecutionAllowed_revertGate_pre s₄) s₅ ∧
      -- 6. frame: revived gate output merged onto the caller's varstore.
      State.setStore (🧟s₅) (Ok evm store) = s₉

lemma fun_requireExecutionAllowed_abs_of_concrete {s₀ s₉ : State} { var_bundleHash var__interopBundle_mpos} :
  Spec (fun_requireExecutionAllowed_concrete_of_code.1  var_bundleHash var__interopBundle_mpos) s₀ s₉ →
  Spec (A_fun_requireExecutionAllowed  var_bundleHash var__interopBundle_mpos) s₀ s₉ := by
  unfold fun_requireExecutionAllowed_concrete_of_code A_fun_requireExecutionAllowed
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hconcrete
  clr_funargs at hconcrete
  -- Resolve the straight-line prologue lookups to their closed forms.
  simp only [insert_Ok', evm_Ok'] at hconcrete
  simp (config := { decide := true }) only
    [lookup_insert_self_fin', lookup_insert_ne_fin'] at hconcrete
  intro evmA storeA hok
  cases hok
  obtain ⟨s₁, h1, s₂, h2, s₃, h3, s₄, h4, s₅, h5, hmerge⟩ := hconcrete
  exact ⟨s₁, h1, s₂, h2, s₃, h3, s₄, h4, s₅, h5, hmerge⟩

end

end generated.InteropHandler.InteropHandler
