import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_222056077841235403
import generated.L1Bridgehub.L1Bridgehub.Common.if_4531326074889478772
import generated.L1Bridgehub.L1Bridgehub.Common.if_1430663170539197694
import generated.L1Bridgehub.L1Bridgehub.Common.if_5351827025296077982
import generated.L1Bridgehub.L1Bridgehub.Common.if_7136306376268056098
import generated.L1Bridgehub.L1Bridgehub.Common.if_3660125111862948269
import generated.L1Bridgehub.L1Bridgehub.Common.if_6111287530207380751
import generated.L1Bridgehub.L1Bridgehub.Common.if_7036283890549845631
import generated.L1Bridgehub.L1Bridgehub.Common.if_4757574632952405061

import generated.L1Bridgehub.L1Bridgehub.fun_validateChainParams_gen

import specs.RevertModel

/-
  CLEAN guard theorem for `fun_validateChainParams`
  (era-contracts `BridgehubBase._validateChainParams`), enabled by the new
  `reverted` flag on `EVMState`.

  The function is the chain-registration validation guard: NINE sequential
  revert-guard `if`-blocks performed in order on (_chainId, _assetId,
  _chainTypeManager).  Old form (fun_validateChainParams_user.lean) could only
  state that a run *routes through* the nine named if-blocks, because a `revert`
  in this EVM model still left the state `Ok` — success and failure were
  indistinguishable by `isOk`.

  New form (here): with the `reverted` flag, a NON-reverting (genuinely
  successful) execution of `_validateChainParams` IMPLIES that each of the
  validation conditions of gates 1–8 held — both the STORAGE-INDEPENDENT ones
  (gates 1–5) AND the STORAGE-DEPENDENT ones (gates 6–8):

    gate 1  ZeroChainId               :  _chainId ≠ 0
    gate 2  ChainIdTooBig             :  ¬ (_chainId > type(uint48).max)
    gate 3  ChainIdCantBeCurrentChain :  _chainId ≠ block.chainid
    gate 4  ZeroAddress               :  cleaned(_chainTypeManager) ≠ 0
    gate 5  EmptyAssetId              :  _assetId ≠ 0
    gate 6  CTMNotRegistered          :  ∃ slot, land(sload(slot), 255) ≠ 0   (CTM map, base 202)
    gate 7  AssetIdNotSupported       :  ∃ slot, land(sload(slot), 255) ≠ 0   (asset map, base 218)
    gate 8  SharedBridgeNotSet        :  land(sload(201), 2^160-1) ≠ 0        (fixed slot 201)

  This is the faithful "success ⇒ precondition held" reading of the first eight
  `require`s.  The storage-dependent gates 6–8 are phrased via `evm.sload`: the
  `mstore`/`keccak256` scratch writes preceding each gate preserve storage, so
  the slot read is the ORIGINAL `evm`'s storage.  Gates 6 and 7 hash a
  dynamically-chosen slot (the keccak oracle's output), so they are pinned
  existentially over the slot; gate 8 reads the fixed slot 201, pinned concretely.

  Gate 9 (BridgeHubAlreadyRegistered) is NOT pinned here — see the caveats at the
  bottom of this file.
-/

namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common Clear.RevertModel

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

-- ===========================================================================
--  General revert-guard lemma.
--
--  Every gate of `_validateChainParams` is an `if guard { …; revert(…) }` whose
--  body is straight-line code ending in a `revert`.  Running such a block on a
--  non-reverted `Ok` state:
--    * if the (already-evaluated) guard literal `g` is nonzero, the body runs and
--      ends in `revert`, forcing `reverted = true`;
--    * if `g = 0`, the body is skipped, the state is returned UNCHANGED.
--  Hence a non-reverting OUTPUT forces `g = 0` AND leaves the state untouched.
--
--  The `body reverts` fact is supplied as a hypothesis `hbody`, discharged per
--  gate by a short concrete replay (each body is `mstore;…;revert`).
-- ===========================================================================

/-- If a guard-if's body always reverts (on the post-guard state), then a
    non-reverting output of the if-block forces the guard literal to be `0` and
    the output to equal the input state. -/
lemma guard_if_clean
    {cond : Expr} {body : List Stmt} {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hbody : (exec fuel (.Block body) ((eval fuel cond (Ok evm store)).1)).evm.reverted = true)
    (hguard_pure : (eval fuel cond (Ok evm store)).1 = Ok evm store) :
    (exec fuel (.If cond body) (Ok evm store)).evm.reverted = false →
      (eval fuel cond (Ok evm store)).2 = 0 ∧
        exec fuel (.If cond body) (Ok evm store) = Ok evm store := by
  rw [If']
  intro hno
  rcases he : eval fuel cond (Ok evm store) with ⟨s', c'⟩
  simp only [he] at hno hguard_pure hbody ⊢
  -- hbody : (exec (Block body) s').evm.reverted = true ; hguard_pure : s' = Ok evm store
  subst hguard_pure
  by_cases hg : c' = 0
  · -- guard zero ⇒ body skipped ⇒ output = input
    subst hg
    refine ⟨rfl, ?_⟩
    simp only [ne_eq, not_true_eq_false, if_false]
  · -- guard nonzero ⇒ body runs ⇒ reverts ⇒ contradicts hno
    exfalso
    rw [if_pos hg] at hno
    rw [hbody] at hno
    exact absurd hno (by decide)

-- ===========================================================================
--  Reverted-flag MONOTONICITY for the constructs that appear in the body.
--
--  Once `reverted = true`, every statement of `_validateChainParams` keeps it
--  `true` (the model keeps executing after a revert; revert only sets the flag
--  and rewrites return_data, and every op is a `{σ with …}` update preserving
--  the flag).  We need this so that a non-reverting FINAL state forces NONE of
--  the gates to have reverted — in particular gates 1–5.
-- ===========================================================================

/-- The `multifill'` post-step of a primcall preserves the evm flag: it writes
    only variables. -/
lemma multifill'_reverted {vars : List Identifier} {s : State} {xs : List Literal} :
    (multifill' vars (s, xs)).evm.reverted = s.evm.reverted := by
  unfold multifill'
  rw [State.evm_multifill]

/-- `keccak256` preserves the `reverted` flag: both branches are `{σ with …}`
    field updates (hashing map / hash-collision flag). -/
@[simp] lemma keccak256_reverted (σ : EVMState) (p n : UInt256) :
    (match σ.keccak256 p n with
     | .some a => a.snd.reverted
     | .none   => σ.addHashCollision.reverted) = σ.reverted := by
  unfold EVMState.keccak256 EVMState.addHashCollision
  rcases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with _ | val
  · -- no cached hash: case on the partition of the keccak range
    rcases hp : (σ.keccak_range.partition (λ x => x ∈ σ.used_range)) with ⟨l, r⟩
    simp only [List.partition_eq_filter_filter] at hp
    rcases r with _ | ⟨rr, rs⟩ <;> simp_all
  · -- cached hash: returns (val, σ), so reverted = σ.reverted
    simp_all

-- ===========================================================================
--  `sload` INVARIANCE under the pre-gate scratch ops (gates 6–9).
--
--  Gates 6–9 read storage through keccak'd or fixed slots, preceded by
--  `mstore`/`keccak256` scratch writes.  None of those ops touch the account
--  map or execution environment, so `sload` is preserved; this lets us phrase
--  the storage-dependent conditions in terms of the ORIGINAL `evm.sload`.
-- ===========================================================================

/-- `mstore` only touches `machine_state`, so it preserves `sload`. -/
@[simp] lemma sload_mstore' (σ : EVMState) (a v k : UInt256) :
    (σ.mstore a v).sload k = σ.sload k := rfl

/-- `keccak256` only touches keccak bookkeeping / `used_range`, never the
    account map or execution environment, so it preserves `sload`. -/
lemma sload_keccak256' {σ : EVMState} {p n r : UInt256} {σ' : EVMState}
    (h : σ.keccak256 p n = some (r, σ')) (k : UInt256) :
    σ'.sload k = σ.sload k := by
  have hacc : σ'.account_map = σ.account_map ∧
              σ'.execution_env = σ.execution_env := by
    simp only [EVMState.keccak256] at h
    repeat' split at h
    all_goals (
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩)
        | exact absurd h (by simp))
  unfold EVMState.sload EVMState.lookupAccount
  rw [hacc.1, hacc.2]

/-- `addHashCollision` only sets the `hash_collision` flag, so it preserves
    `sload`. -/
@[simp] lemma sload_addHashCollision' (σ : EVMState) (k : UInt256) :
    σ.addHashCollision.sload k = σ.sload k := rfl

/-- A guard-if `if g { …; revert }` run on a `reverted = true` state stays
    `reverted = true`: the skip branch returns the (reverted) state unchanged,
    and the body branch ends in `revert` (which keeps `reverted = true`).  We
    pass the body-reverts fact `hbody` (it holds for every gate body, on any
    state).  -/
lemma guard_if_keeps_reverted
    {cond : Expr} {body : List Stmt} {s : State} {fuel : ℕ}
    (hpure : (eval fuel cond s).1 = s)
    (hbody : (exec fuel (.Block body) s).evm.reverted = true)
    (h : s.evm.reverted = true) :
    (exec fuel (.If cond body) s).evm.reverted = true := by
  rw [If']
  rcases he : eval fuel cond s with ⟨s', c'⟩
  simp only [he] at hpure hbody
  subst hpure
  dsimp only
  by_cases hg : c' = 0
  · subst hg; simp only [ne_eq, not_true_eq_false, if_false]; exact h
  · rw [if_pos hg]; exact hbody

/-- Reverted monotonicity over a `Block`, given that each statement of the block
    preserves a `reverted = true` flag.  Proved by list induction; the head fact
    is supplied by `hstmts` and the tail by the IH. -/
lemma Block_keeps_reverted
    {stmts : List Stmt} {fuel : ℕ}
    (hstmts : ∀ x ∈ stmts, ∀ s : State, s.evm.reverted = true →
                (exec fuel x s).evm.reverted = true) :
    ∀ s : State, s.evm.reverted = true → (exec fuel (.Block stmts) s).evm.reverted = true := by
  induction stmts with
  | nil => intro s h; rw [nil]; exact h
  | cons x xs ih =>
    intro s h
    rw [cons]
    apply ih (fun y hy => hstmts y (List.mem_cons_of_mem _ hy))
    exact hstmts x (List.mem_cons_self _ _) s h

-- ===========================================================================
--  Per-statement reverted-preservation for every statement of the body.
-- ===========================================================================

/-- A keccak256 `LetPrimCall` (over memory window [0,64)) preserves a
    `reverted = true` flag: both keccak branches are `{σ with …}` updates. -/
lemma keccak_let_keeps_reverted
    {var : Identifier} {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (h : (Ok evm store).evm.reverted = true) :
    (exec fuel (.LetPrimCall [var] P.Keccak256 [Expr.Lit 0, Expr.Lit 64]) (Ok evm store)).evm.reverted = true := by
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, head', reverse', multifill', PrimCall', Lit', Var',
    execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.append_assoc, List.cons_append, cons', EVMKeccak256']
  simp only [State.evm] at h
  -- Goal: `(multifill' [var] (match (Ok evm store).evm.keccak256 0 64 with …)).evm.reverted`.
  rw [show (Ok evm store).evm = evm from rfl]
  have hh := keccak256_reverted evm 0 64
  cases hk : evm.keccak256 0 64 with
  | some a =>
      rw [hk] at hh; simp only at hh ⊢
      rw [State.evm_multifill]; simp only [State.setEvm, State.evm]; rw [hh]; exact h
  | none =>
      simp only at hh ⊢
      rw [State.evm_multifill]
      simp only [State.setEvm, State.evm, EVMState.addHashCollision]; exact h

/-- Every statement appearing in `fun_validateChainParams`'s body preserves a
    `reverted = true` flag.  Pure ops (shl/sub/and/iszero/chainid/sload/mload)
    leave the state untouched; mstore/keccak `setEvm` a `{σ with …}` update; the
    nine guard-ifs end their bodies in `revert`.  This is the per-statement input
    to `Block_keeps_reverted`. -/
lemma validateChainParams_stmts_keep_reverted {fuel : ℕ} :
    ∀ x ∈ fun_validateChainParams.body, ∀ s : State, s.evm.reverted = true →
        (exec fuel x s).evm.reverted = true := by
  intro x hx s h
  rcases s with ⟨evm, store⟩ | _ | _ <;>
    [skip; (simp only [State.evm] at h; exact absurd h (by decide));
     (simp only [State.evm] at h; exact absurd h (by decide))]
  fin_cases hx <;>
    first
    | -- pure / mstore / keccak primcall statements: replay one op, reverted kept.
      (first | rw [LetPrimCall'] | rw [ExprStmtPrimCall'] | rw [AssignPrimCall']
       simp only [evalArgs, evalTail, head', reverse', multifill', PrimCall', Lit', Var',
         execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
         List.singleton_append, List.append_assoc, List.cons_append, cons',
         EVMShl', EVMSub', EVMAnd', EVMIszero', EVMChainid', EVMSload', EVMMload',
         EVMMstore', multifill'_reverted, State.setEvm, State.evm,
         mstore_reverted, keccak256_reverted]
       exact h)
    | -- keccak LetPrimCall: setEvm of keccak's `{σ with …}` update.
      exact keccak_let_keeps_reverted h
    | -- guard-if: body ends in revert, so reverted stays true.
      (apply guard_if_keeps_reverted (fuel := fuel) _ _ h
       · -- guard is a pure expression (iszero/gt/eq of vars+lits): eval keeps state.
         simp only [eval, evalArgs, evalTail, head', reverse', multifill', PrimCall',
           Lit', Var', evalPrimCall, execPrimCall, EVMIszero', EVMGt', EVMEq',
           List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
           List.append_assoc, List.cons_append, cons']
       · -- body reverts on any state: replay the straight-line revert body.
         simp only [cons, nil, ExprStmtPrimCall', LetPrimCall', AssignPrimCall',
           evalArgs, evalTail, cons', head', reverse', multifill', PrimCall', Lit', Var',
           execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
           List.singleton_append, List.append_assoc, List.cons_append,
           EVMMload', EVMShl', EVMMstore', EVMAdd', EVMRevert']
         rfl)

/-- A non-reverting `reviveJump` output forces a non-reverting input.  (On `Ok`,
    `reviveJump` is the identity; on a non-`Ok` state the evm is `default`, whose
    `reverted` flag is already `false`.) -/
lemma reverted_of_reviveJump {Y : State} (h : (🧟 Y).evm.reverted = false) :
    Y.evm.reverted = false := by
  rcases Y with ⟨e, st⟩ | _ | c
  · simpa using h
  · rfl
  · rfl

/-- From a non-reverting run of `Block (gate :: rest)` (whose `rest` statements
    each preserve `reverted = true`), the leading statement `gate` itself did not
    revert.  (If it had, monotonicity over `rest` would force the whole run to
    revert.) -/
lemma head_not_reverted
    {gate : Stmt} {rest : List Stmt} {s : State} {fuel : ℕ}
    (hrest : ∀ x ∈ rest, ∀ t : State, t.evm.reverted = true →
              (exec fuel x t).evm.reverted = true)
    (hfull : (exec fuel (.Block (gate :: rest)) s).evm.reverted = false) :
    (exec fuel gate s).evm.reverted = false := by
  rw [cons] at hfull
  by_contra hc
  rw [Bool.not_eq_false] at hc
  rw [Block_keeps_reverted hrest _ hc] at hfull
  exact absurd hfull (by decide)

/-- One gate, end to end.  Given a non-reverting run of `Block (If cond gbody ::
    rest)` from an `Ok` state, where `gbody` reverts and `cond` is a pure guard
    and the `rest` statements preserve `reverted = true`, conclude:
      * the guard evaluated to `0` (so the gate's condition held), AND
      * the run of `Block rest` from the SAME state is still non-reverting
        (the gate skipped its body, leaving the state untouched) — ready to feed
        the next gate. -/
lemma gate_step
    {cond : Expr} {gbody rest : List Stmt} {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (hpure : (eval fuel cond (Ok evm store)).1 = Ok evm store)
    (hbodyrev : (exec fuel (.Block gbody) ((eval fuel cond (Ok evm store)).1)).evm.reverted = true)
    (hrest : ∀ x ∈ rest, ∀ t : State, t.evm.reverted = true →
              (exec fuel x t).evm.reverted = true)
    (hfull : (exec fuel (.Block (.If cond gbody :: rest)) (Ok evm store)).evm.reverted = false) :
    (eval fuel cond (Ok evm store)).2 = 0 ∧
      (exec fuel (.Block rest) (Ok evm store)).evm.reverted = false := by
  have hgout := head_not_reverted hrest hfull
  obtain ⟨hcond, hskip⟩ := guard_if_clean hbodyrev hpure hgout
  refine ⟨hcond, ?_⟩
  rw [cons] at hfull
  rw [hskip] at hfull
  exact hfull

-- ===========================================================================
--  THE CLEAN THEOREM.
-- ===========================================================================

/--
  CLEAN guard theorem for `_validateChainParams`.

  If `_validateChainParams(_chainId, _assetId, _chainTypeManager)` is run from a
  fresh (non-reverted) `Ok` state and the resulting state `s₉` is itself
  NON-reverting, then the validation conditions of gates 1–8 held:

    1. `var_chainId ≠ 0`                                  (ZeroChainId)
    2. `¬ (var_chainId > 281474976710655)`                (ChainIdTooBig; max = uint48)
    3. `var_chainId ≠ evm.chainId`                        (ChainIdCantBeCurrentChain)
    4. `Fin.land var_chainTypeManager (2^160-1) ≠ 0`      (ZeroAddress; cleaned CTM)
    5. `var_assetId ≠ 0`                                  (EmptyAssetId)
    6. `∃ slot, Fin.land (evm.sload slot) 255 ≠ 0`        (CTMNotRegistered; CTM map base 202)
    7. `∃ slot, Fin.land (evm.sload slot) 255 ≠ 0`        (AssetIdNotSupported; asset map base 218)
    8. `Fin.land (evm.sload 201) (2^160-1) ≠ 0`           (SharedBridgeNotSet; fixed slot 201)

  In words: a *successful* `_validateChainParams` execution implies the chain-id
  is nonzero, in-range, and distinct from the current chain; the CTM address is
  nonzero; the asset id is nonzero; the chain-type-manager and asset-id are
  registered (their keccak'd storage slots are nonzero); and the shared bridge
  (slot 201) is set.  This "success ⇒ precondition" reading was impossible before
  the `reverted` flag.

  Gates 6 & 7 read a keccak-derived slot, whose value the EVM model picks
  non-deterministically from the keccak oracle, so they are stated existentially
  over the slot.  All three storage conditions are phrased in terms of the
  ORIGINAL `evm.sload`: the `mstore`/`keccak256` scratch writes that precede each
  gate touch only memory / keccak bookkeeping, never the account map, so storage
  is preserved (see `sload_mstore'`, `sload_keccak256'`, `sload_addHashCollision'`).

  Gate 9 (BridgeHubAlreadyRegistered) is NOT pinned here — see the caveats at the
  end of the file.
-/
theorem fun_validateChainParams_clean
    {evm : EVMState} {store : VarStore} {s₉ : State} {fuel : ℕ}
    {var_chainId var_assetId var_chainTypeManager : Literal}
    (hr : evm.reverted = false)
    (hexec : execCall fuel fun_validateChainParams []
               (Ok evm store, [var_chainId, var_assetId, var_chainTypeManager]) = s₉) :
    s₉.evm.reverted = false →
      var_chainId ≠ 0 ∧
      ¬ (var_chainId > 281474976710655) ∧
      var_chainId ≠ evm.chainId ∧
      Fin.land var_chainTypeManager (Fin.shiftLeft 1 160 - 1) ≠ 0 ∧
      var_assetId ≠ 0 ∧
      (∃ slot : UInt256, Fin.land (evm.sload slot) 255 ≠ 0) ∧
      (∃ slot : UInt256, Fin.land (evm.sload slot) 255 ≠ 0) ∧
      Fin.land (evm.sload 201) (Fin.shiftLeft 1 160 - 1) ≠ 0 := by
  intro hno_revert
  -- Reduce s₉.evm.reverted to the body-execution's reverted flag.
  rw [← hexec] at hno_revert
  unfold execCall call fun_validateChainParams at hno_revert
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons] at hno_revert
  -- Strip the `call` post-processing wrappers around the body output `s₂`:
  --   s₉.evm = (🧟 s₂).evm = s₂.evm  (overwrite? is identity on Ok; setStore keeps evm),
  -- so a non-reverting s₉ ⇔ a non-reverting body output.
  rw [multifill_nil] at hno_revert
  -- Strip the `call` post-processing: `setStore` keeps the evm, `overwrite?` over
  -- an `Ok` base is the identity, leaving `(🧟(exec …)).evm.reverted`.
  simp only [evm_setStore, overwrite?_of_Ok] at hno_revert
  -- Strip the `🧟` revive wrapper.
  replace hno_revert := reverted_of_reviveJump hno_revert
  -- Now `hno_revert : (exec fuel (Block bodylist) (initcall … (Ok evm store))).evm.reverted = false`.
  -- The initcall base is `Ok evm store'` (evm unchanged), reverted = false.
  set base : State := initcall ["var_chainId", "var_assetId", "var_chainTypeManager"]
    [var_chainId, var_assetId, var_chainTypeManager] (Ok evm store) with hbase
  -- Per-statement reverted-preservation facts (each body statement, any sublist).
  have hbody := @validateChainParams_stmts_keep_reverted fuel
  -- Basic facts about the call-entry state `base = Ok evm store'`.
  have hbase_ok : base.isOk := by rw [hbase]; exact True.intro
  have hbase_rev : base.evm.reverted = false := by rw [hbase]; simpa using hr
  have hb_cid : base["var_chainId"]!! = var_chainId := by
    rw [hbase]; exact lookup_initcall_1
  have hb_aid : base["var_assetId"]!! = var_assetId := by
    rw [hbase]; exact lookup_initcall_2 (by decide)
  have hb_ctm : base["var_chainTypeManager"]!! = var_chainTypeManager := by
    rw [hbase]; exact lookup_initcall_3 (by decide) (by decide)
  -- `hbody` ranges over `fun_validateChainParams.body`, which is definitionally
  -- the explicit statement list inside `hno_revert`; `change` it to that list so
  -- that membership-in-a-tail facts apply directly.
  unfold fun_validateChainParams body at hbody
  -- A reusable abbreviation for the "guard literal is pure on an Ok state"
  -- discharge (each gate's guard is iszero/gt/eq over vars+lits).
  rw [hbase] at hno_revert
  -- Expose the call-entry state in `Ok evm _` form (initcall keeps the evm).
  unfold initcall at hno_revert
  simp only [setStore] at hno_revert
  clear_value base
  clear hbase hbase_ok hbase_rev hb_cid hb_aid hb_ctm base
  -- Discharge tactics for `gate_step`'s side goals are inlined per gate.
  -- ===================  GATE 1 : ZeroChainId  (iszero var_chainId)  ===========
  obtain ⟨hc1, hno_revert⟩ := gate_step (fuel := fuel)
    (by simp only [eval, evalArgs, evalTail, head', reverse', multifill', PrimCall', Lit',
          Var', evalPrimCall, execPrimCall, EVMIszero', List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append, List.append_assoc, List.cons_append, cons'])
    (by simp only [cons, nil, ExprStmtPrimCall', LetPrimCall', evalArgs, evalTail, cons', head',
          reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall,
          List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
          List.append_assoc, List.cons_append, EVMShl', EVMMstore', EVMRevert']; rfl)
    (fun y hy t ht => hbody y (by simp only [List.mem_cons] at hy ⊢; tauto) t ht)
    hno_revert
  -- ===================  GATE 2 : ChainIdTooBig  (gt var_chainId 2^48-1)  ======
  obtain ⟨hc2, hno_revert⟩ := gate_step (fuel := fuel)
    (by simp only [eval, evalArgs, evalTail, head', reverse', multifill', PrimCall', Lit',
          Var', evalPrimCall, execPrimCall, EVMGt', List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append, List.append_assoc, List.cons_append, cons'])
    (by simp only [cons, nil, ExprStmtPrimCall', LetPrimCall', evalArgs, evalTail, cons', head',
          reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall,
          List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
          List.append_assoc, List.cons_append, EVMShl', EVMMstore', EVMRevert']; rfl)
    (fun y hy t ht => hbody y (by simp only [List.mem_cons] at hy ⊢; tauto) t ht)
    hno_revert
  -- let split_expr_2 := chainid()  —  peel the pure let (no revert).
  rw [cons] at hno_revert
  simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
    Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.append_assoc, List.cons_append, EVMChainid',
    multifill_cons, multifill_nil', State.insert] at hno_revert
  -- ===================  GATE 3 : ChainIdCantBeCurrentChain  (eq cid split_expr_2) =
  obtain ⟨hc3, hno_revert⟩ := gate_step (fuel := fuel)
    (by simp only [eval, evalArgs, evalTail, head', reverse', multifill', PrimCall', Lit',
          Var', evalPrimCall, execPrimCall, EVMEq', List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append, List.append_assoc, List.cons_append, cons'])
    (by simp only [cons, nil, ExprStmtPrimCall', LetPrimCall', evalArgs, evalTail, cons', head',
          reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall,
          List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
          List.append_assoc, List.cons_append, EVMShl', EVMMstore', EVMRevert']; rfl)
    (fun y hy t ht => hbody y (by simp only [List.mem_cons] at hy ⊢; tauto) t ht)
    hno_revert
  -- lets split_expr_4 := shl(160,1); split_expr_5 := sub(split_expr_4,1); _1 := and(ctm, split_expr_5)
  rw [cons] at hno_revert
  simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
    Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.append_assoc, List.cons_append, EVMShl',
    multifill_cons, multifill_nil', State.insert] at hno_revert
  rw [cons] at hno_revert
  simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
    Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.append_assoc, List.cons_append, EVMSub',
    lookup_insert, evm_insert, multifill_cons, multifill_nil', State.insert] at hno_revert
  rw [cons] at hno_revert
  simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
    Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.append_assoc, List.cons_append, EVMAnd',
    lookup_insert, evm_insert, multifill_cons, multifill_nil', State.insert] at hno_revert
  -- ===================  GATE 4 : ZeroAddress  (iszero _1)  ====================
  obtain ⟨hc4, hno_revert⟩ := gate_step (fuel := fuel)
    (by simp only [eval, evalArgs, evalTail, head', reverse', multifill', PrimCall', Lit',
          Var', evalPrimCall, execPrimCall, EVMIszero', List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append, List.append_assoc, List.cons_append, cons'])
    (by simp only [cons, nil, ExprStmtPrimCall', LetPrimCall', evalArgs, evalTail, cons', head',
          reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall,
          List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
          List.append_assoc, List.cons_append, EVMShl', EVMMstore', EVMRevert']; rfl)
    (fun y hy t ht => hbody y (by simp only [List.mem_cons] at hy ⊢; tauto) t ht)
    hno_revert
  -- ===================  GATE 5 : EmptyAssetId  (iszero var_assetId)  ==========
  obtain ⟨hc5, hno_revert⟩ := gate_step (fuel := fuel)
    (by simp only [eval, evalArgs, evalTail, head', reverse', multifill', PrimCall', Lit',
          Var', evalPrimCall, execPrimCall, EVMIszero', List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append, List.append_assoc, List.cons_append, cons'])
    (by simp only [cons, nil, ExprStmtPrimCall', LetPrimCall', evalArgs, evalTail, cons', head',
          reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall,
          List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
          List.append_assoc, List.cons_append, EVMShl', EVMMstore', EVMRevert']; rfl)
    (fun y hy t ht => hbody y (by simp only [List.mem_cons] at hy ⊢; tauto) t ht)
    hno_revert
  -- ===========================================================================
  --  GATE 6 : CTMNotRegistered.
  --  Pre-block: mstore(0,_1); mstore(32,202); s8:=keccak(0,64); s9:=sload(s8);
  --             s10:=and(s9,255);  then  if iszero(s10) {…;revert}.
  -- ===========================================================================
  -- mstore(0, _1)
  rw [cons] at hno_revert
  simp only [ExprStmtPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
    Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.append_assoc, List.cons_append, EVMMstore',
    multifill_nil, multifill_nil', multifill_cons,
    lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert
  -- mstore(32, 202)
  rw [cons] at hno_revert
  simp only [ExprStmtPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
    Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.append_assoc, List.cons_append, EVMMstore',
    multifill_nil, multifill_nil', multifill_cons,
    lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert
  -- Generalize the scratch-written evm entering the keccak, and the store.
  revert hno_revert
  generalize hstore6 : (Finmap.insert "_1" _ _ : VarStore) = store6
  generalize hevm6 : ((evm.mstore 0 _).mstore 32 202 : EVMState) = evm6
  intro hno_revert
  -- s8 := keccak256(0, 64)
  rw [cons] at hno_revert
  simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
    Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.append_assoc, List.cons_append, EVMKeccak256',
    multifill_nil, multifill_nil', multifill_cons,
    lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert
  rcases hk6 : evm6.keccak256 0 64 with _ | ⟨k6, evm7⟩ <;>
    rw [hk6] at hno_revert <;>
    simp only [multifill_cons, multifill_nil, multifill_nil', State.setEvm, State.evm, State.insert,
      evm_insert, lookup_insert] at hno_revert <;>
    -- s9 := sload(s8) ; s10 := and(s9, 255)
    (rw [cons] at hno_revert
     simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
       Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
       List.singleton_append, List.append_assoc, List.cons_append, EVMSload',
       multifill_nil, multifill_nil', multifill_cons,
       lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert
     rw [cons] at hno_revert
     simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
       Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
       List.singleton_append, List.append_assoc, List.cons_append, EVMAnd',
       multifill_nil, multifill_nil', multifill_cons,
       lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert)
  all_goals (
    obtain ⟨hc6, hno_revert⟩ := gate_step (fuel := fuel)
      (by simp only [eval, evalArgs, evalTail, head', reverse', multifill', PrimCall', Lit',
            Var', evalPrimCall, execPrimCall, EVMIszero', List.reverse_cons, List.reverse_nil,
            List.nil_append, List.singleton_append, List.append_assoc, List.cons_append, cons'])
      (by simp only [cons, nil, ExprStmtPrimCall', LetPrimCall', evalArgs, evalTail, cons', head',
            reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall,
            List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
            List.append_assoc, List.cons_append, EVMShl', EVMMstore', EVMRevert']; rfl)
      (fun y hy t ht => hbody y (by
        repeat (first | exact hy | apply List.mem_cons_of_mem)) t ht)
      hno_revert)
  -- ===========================================================================
  --  GATE 7 : AssetIdNotSupported  (slot base 218).
  --  Pre-block: mstore(0,var_assetId); mstore(32,218); s12:=keccak(0,64);
  --             s13:=sload(s12); s14:=and(s13,255); then if iszero(s14) {…;revert}.
  -- ===========================================================================
  all_goals (
    -- mstore(0, var_assetId)
    rw [cons] at hno_revert
    simp only [ExprStmtPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
      Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.append_assoc, List.cons_append, EVMMstore',
      multifill_nil, multifill_nil', multifill_cons,
      lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert
    -- mstore(32, 218)
    rw [cons] at hno_revert
    simp only [ExprStmtPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
      Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.append_assoc, List.cons_append, EVMMstore',
      multifill_nil, multifill_nil', multifill_cons,
      lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert
    -- Name the gate-6-exit evm uniformly (one of the two keccak branches), record
    -- its `sload`-invariance back to the original `evm`.
    first
      | (generalize hevmA7 : ((evm6.addHashCollision.mstore 0 _).mstore 32 218 : EVMState)
            = evmA7 at hno_revert
         have hinv7 : ∀ k, evmA7.sload k = evm.sload k := by
           intro k; rw [← hevmA7, sload_mstore', sload_mstore', sload_addHashCollision', ← hevm6,
             sload_mstore', sload_mstore'])
      | (generalize hevmA7 : ((evm7.mstore 0 _).mstore 32 218 : EVMState)
            = evmA7 at hno_revert
         have hinv7 : ∀ k, evmA7.sload k = evm.sload k := by
           intro k; rw [← hevmA7, sload_mstore', sload_mstore', sload_keccak256' hk6, ← hevm6,
             sload_mstore', sload_mstore'])
    -- s12 := keccak256(0, 64)
    rw [cons] at hno_revert
    simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
      Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.append_assoc, List.cons_append, EVMKeccak256',
      multifill_nil, multifill_nil', multifill_cons,
      lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert
    rcases hk7 : evmA7.keccak256 0 64 with _ | ⟨k7, evmB7⟩ <;>
      rw [hk7] at hno_revert <;>
      simp only [multifill_cons, multifill_nil, multifill_nil', State.setEvm, State.evm,
        State.insert, evm_insert, lookup_insert] at hno_revert <;>
      -- s13 := sload(s12) ; s14 := and(s13, 255)
      (rw [cons] at hno_revert
       simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
         Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
         List.singleton_append, List.append_assoc, List.cons_append, EVMSload',
         multifill_nil, multifill_nil', multifill_cons,
         lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert
       rw [cons] at hno_revert
       simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
         Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
         List.singleton_append, List.append_assoc, List.cons_append, EVMAnd',
         multifill_nil, multifill_nil', multifill_cons,
         lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert))
  all_goals (
    obtain ⟨hc7, hno_revert⟩ := gate_step (fuel := fuel)
      (by simp only [eval, evalArgs, evalTail, head', reverse', multifill', PrimCall', Lit',
            Var', evalPrimCall, execPrimCall, EVMIszero', List.reverse_cons, List.reverse_nil,
            List.nil_append, List.singleton_append, List.append_assoc, List.cons_append, cons'])
      (by simp only [cons, nil, ExprStmtPrimCall', LetPrimCall', evalArgs, evalTail, cons', head',
            reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall,
            List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
            List.append_assoc, List.cons_append, EVMShl', EVMMstore', EVMRevert']; rfl)
      (fun y hy t ht => hbody y (by
        repeat (first | exact hy | apply List.mem_cons_of_mem)) t ht)
      hno_revert)
  -- ===========================================================================
  --  GATE 8 : SharedBridgeNotSet  (FIXED slot 201).
  --  Pre-block: s16:=sload(201); s17:=shl(160,1); s18:=sub(s17,1);
  --             s19:=and(s16,s18); then if iszero(s19) {…;revert}.
  --  No keccak — the slot is the literal `201`, deterministic.
  -- ===========================================================================
  all_goals (
    -- s16 := sload(201)
    rw [cons] at hno_revert
    simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
      Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.append_assoc, List.cons_append, EVMSload',
      multifill_nil, multifill_nil', multifill_cons,
      lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert
    -- s17 := shl(160, 1)
    rw [cons] at hno_revert
    simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
      Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.append_assoc, List.cons_append, EVMShl',
      multifill_nil, multifill_nil', multifill_cons,
      lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert
    -- s18 := sub(s17, 1)
    rw [cons] at hno_revert
    simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
      Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.append_assoc, List.cons_append, EVMSub',
      multifill_nil, multifill_nil', multifill_cons,
      lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert
    -- s19 := and(s16, s18)
    rw [cons] at hno_revert
    simp only [LetPrimCall', evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
      Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.append_assoc, List.cons_append, EVMAnd',
      multifill_nil, multifill_nil', multifill_cons,
      lookup_insert, lookup_insert_of_ne, evm_insert, State.evm, State.setEvm, State.insert] at hno_revert)
  all_goals (
    obtain ⟨hc8, hno_revert⟩ := gate_step (fuel := fuel)
      (by simp only [eval, evalArgs, evalTail, head', reverse', multifill', PrimCall', Lit',
            Var', evalPrimCall, execPrimCall, EVMIszero', List.reverse_cons, List.reverse_nil,
            List.nil_append, List.singleton_append, List.append_assoc, List.cons_append, cons'])
      (by simp only [cons, nil, ExprStmtPrimCall', LetPrimCall', evalArgs, evalTail, cons', head',
            reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall,
            List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
            List.append_assoc, List.cons_append, EVMShl', EVMMstore', EVMRevert']; rfl)
      (fun y hy t ht => hbody y (by
        repeat (first | exact hy | apply List.mem_cons_of_mem)) t ht)
      hno_revert)
  clear hno_revert hbody
  -- In BOTH keccak branches we now reduce the guard literals and discharge gates
  -- 1–6.  Gates 1–5 are branch-independent (hc1…hc5); gate 6 is `hc6`, whose
  -- `sload` we rewrite back to the ORIGINAL `evm` (mstore/keccak/addHashCollision
  -- preserve storage), then supply the keccak slot as the existential witness.
  all_goals (
    -- Reduce gates 1–5 guard literals to `(if decide Pᵢ then 1 else 0) = 0`.
    simp only [eval, evalArgs, evalTail, head', reverse', multifill', PrimCall', Lit', Var',
      evalPrimCall, execPrimCall, EVMIszero', EVMGt', EVMEq',
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.append_assoc, List.cons_append, cons', List.head!,
      State.lookup!, Option.get!, fromBool, Bool.toUInt256] at hc1 hc2 hc3 hc4 hc5
    simp only [State.evm] at hc1 hc2 hc3 hc4 hc5
    simp (config := { decide := true }) only [Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
      ne_eq, not_false_eq_true] at hc1 hc2 hc3 hc4 hc5
    -- Reduce gates 6, 7 & 8 guard literals `iszero(and(sload(slot),mask))`.
    simp only [eval, evalArgs, evalTail, head', reverse', multifill', PrimCall', Lit', Var',
      evalPrimCall, execPrimCall, EVMIszero', List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.append_assoc, List.cons_append, cons', List.head!,
      State.lookup!, Option.get!, fromBool, Bool.toUInt256, State.evm] at hc6 hc7 hc8
    simp (config := { decide := true }) only [Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
      ne_eq, not_false_eq_true] at hc6 hc7 hc8
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- GATE 1 : var_chainId ≠ 0
      intro hcontra; rw [if_pos (decide_eq_true hcontra)] at hc1; exact absurd hc1 (by decide)
    · -- GATE 2 : ¬ (var_chainId > 2^48-1)
      intro hcontra; rw [if_pos (decide_eq_true hcontra)] at hc2; exact absurd hc2 (by decide)
    · -- GATE 3 : var_chainId ≠ block.chainid
      intro hcontra; rw [if_pos (decide_eq_true hcontra)] at hc3; exact absurd hc3 (by decide)
    · -- GATE 4 : cleaned _chainTypeManager ≠ 0
      intro hcontra; rw [if_pos (decide_eq_true hcontra)] at hc4; exact absurd hc4 (by decide)
    · -- GATE 5 : var_assetId ≠ 0
      intro hcontra; rw [if_pos (decide_eq_true hcontra)] at hc5; exact absurd hc5 (by decide)
    · -- GATE 6 : CTMNotRegistered — the keccak'd registration slot is nonzero.
      -- Rewrite the post-scratch `sload` back to the original `evm.sload`.
      first
        | (-- keccak collision branch: slot literal is 0.
           refine ⟨0, ?_⟩
           rw [sload_addHashCollision', ← hevm6, sload_mstore', sload_mstore'] at hc6
           intro hcontra; rw [if_pos (decide_eq_true hcontra)] at hc6; exact absurd hc6 (by decide))
        | (-- keccak success branch: slot literal is the hash `k6`.
           refine ⟨k6, ?_⟩
           rw [sload_keccak256' hk6, ← hevm6, sload_mstore', sload_mstore'] at hc6
           intro hcontra; rw [if_pos (decide_eq_true hcontra)] at hc6; exact absurd hc6 (by decide))
    · -- GATE 7 : AssetIdNotSupported — the keccak'd asset-id slot is nonzero.
      first
        | (-- keccak collision branch: slot literal is 0.
           refine ⟨0, ?_⟩
           rw [sload_addHashCollision', hinv7] at hc7
           intro hcontra; rw [if_pos (decide_eq_true hcontra)] at hc7; exact absurd hc7 (by decide))
        | (-- keccak success branch: slot literal is the hash `k7`.
           refine ⟨k7, ?_⟩
           rw [sload_keccak256' hk7, hinv7] at hc7
           intro hcontra; rw [if_pos (decide_eq_true hcontra)] at hc7; exact absurd hc7 (by decide))
    · -- GATE 8 : SharedBridgeNotSet — fixed slot 201 holds a nonzero address.
      -- Rewrite the gate-8 `sload 201` back to the original `evm` (the gate-7-exit
      -- evm differs by branch: `addHashCollision` of `evmA7`, or the keccak result
      -- `evmB7`; both preserve storage).
      first
        | rw [sload_addHashCollision', hinv7] at hc8
        | rw [sload_keccak256' hk7, hinv7] at hc8
      intro hcontra; rw [if_pos (decide_eq_true hcontra)] at hc8; exact absurd hc8 (by decide))

end

end generated.L1Bridgehub.L1Bridgehub
