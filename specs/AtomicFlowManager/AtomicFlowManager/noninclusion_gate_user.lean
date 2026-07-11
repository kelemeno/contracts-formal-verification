import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.fun_hashLeaf
import generated.AtomicFlowManager.AtomicFlowManager.fun_verifyNonInclusion
import specs.AtomicFlowManager.AtomicFlowManager.imt_path_user
import specs.AtomicFlowManager.AtomicFlowManager.imt_path_toplevel_user
import specs.AtomicFlowManager.AtomicFlowManager.imt_leafhash_user

/-
  CLOSED FORM OF `fun_verifyNonInclusion` — the reclaim arm's absence witness
  (bridge-spec points 3/4).

  The function checks an IMT adjacency (non-inclusion) witness:
      require(value ≠ 0)
      require(lowLeaf.key < value)                            -- window left edge
      require(lowLeaf.nextKey = 0 ∨ value < lowLeaf.nextKey)  -- window right edge
      var := eq(calculateRootMemory(proof, index, hashLeaf(lowLeaf)), root)

  On the success path (well-formed window, in-bounds proof) the WHOLE function
  equals: hash the adjacency leaf, fold it up the tree with `foldRoot` (#24),
  and return whether the result matches the authenticated root.  The
  `fun_hashLeaf` step is taken as a pure-call hypothesis `hhl` (its closed form
  is proven for the identical L2InteropCommitmentTree copy and ports later);
  everything else is derived.  Axiom-free.
-/

namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

set_option maxRecDepth 6000
set_option maxHeartbeats 12000000
set_option linter.dupNamespace false

private lemma insert_Ok {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

private lemma evm_Ok {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

private lemma reviveJump_of_isOk' {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok]; exact lookup_insert_of_ne h

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

private lemma lookup_ok_evm {e e' : EVMState} {σ : VarStore} {k : Identifier} :
    (Ok e σ)[k]!! = (Ok e' σ)[k]!! := rfl

/-- The inner window-check body: `split_expr_5 := gt(_2, var_value); expr :=
iszero(split_expr_5)` — with `value < nextKey` it resets `expr` to `0`. -/
private lemma window_body
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {nk val : Literal}
    (h2 : (Ok evm σ)["_2"]!! = nk)
    (hv : (Ok evm σ)["var_value"]!! = val)
    (hgt : nk > val) :
    exec (fuel+1) (.Block [LetPrimCall ["split_expr_5"] P.Gt [Var "_2", Var "var_value"],
        AssignPrimCall ["expr"] P.Iszero [Var "split_expr_5"]]) (Ok evm σ)
      = Ok evm (Finmap.insert "expr" 0 (Finmap.insert "split_expr_5" 1 σ)) := by
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMGt', multifill_cons, multifill_nil]
  rw [h2, hv]
  rw [show fromBool (nk > val) = (1 : UInt256) from by rw [decide_eq_true hgt]; rfl]
  simp only [insert_Ok]
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMIszero', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  simp only [insert_Ok]

/-- The common tail of `fun_verifyNonInclusion` after the window checks:
the (skipped) revert-guard, the `hashLeaf` call, the `calculateRootMemory`
call and the final root comparison. -/
private lemma ni_tail
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    {rootv leafPos idxv proofPos : Literal}
    {hlEvm : EVMState} {hlOut : Literal}
    (hexpr : (Ok evm σ)["expr"]!! = 0)
    (hleaf : (Ok evm σ)["var_lowLeaf_mpos"]!! = leafPos)
    (hproof : (Ok evm σ)["var_lowLeafProof_mpos"]!! = proofPos)
    (hidxl : (Ok evm σ)["var_lowLeafIndex"]!! = idxv)
    (hrootl : (Ok evm σ)["var_root"]!! = rootv)
    (hhl : ∀ σ' : VarStore, execCall (fuel+1) fun_hashLeaf ["split_expr_7"]
        (Ok evm σ', [leafPos]) = Ok hlEvm (σ'.insert "split_expr_7" hlOut))
    (hlt256 : hlEvm.mload proofPos < 256)
    (hidx : idxv < Fin.shiftLeft (1 : UInt256) (hlEvm.mload proofPos))
    (hfuel : 2 * (hlEvm.mload proofPos).val + 2 ≤ fuel)
    (hpath96 : 96 ≤ proofPos.val)
    (hnw : proofPos.val + 32 * (hlEvm.mload proofPos).val + 64 ≤ 2 ^ 256)
    (hdepthlt : (hlEvm.mload proofPos).val < 2 ^ 64) :
    exec (fuel+1) (.Block
        [If (Var "expr")
            [LetPrimCall ["split_expr_6"] P.Shl [Lit 225, Lit 1816069939],
              ExprStmtPrimCall P.Mstore [Lit 0, Var "split_expr_6"],
              ExprStmtPrimCall P.Mstore [Lit 4, Var "_2"],
              ExprStmtPrimCall P.Mstore [Lit 36, Var "var_value"],
              ExprStmtPrimCall P.Revert [Lit 0, Lit 68]],
          LetCall ["split_expr_7"] fun_hashLeaf [Var "var_lowLeaf_mpos"],
          LetCall ["split_expr_8"] fun_calculateRootMemory
            [Var "var_lowLeafProof_mpos", Var "var_lowLeafIndex", Var "split_expr_7"],
          AssignPrimCall ["var"] P.Eq [Var "split_expr_8", Var "var_root"]]) (Ok evm σ)
      = Ok (foldRoot hlEvm proofPos (hlEvm.mload proofPos).val 0 idxv hlOut).2
          (Finmap.insert "var" (fromBool
              ((foldRoot hlEvm proofPos (hlEvm.mload proofPos).val 0 idxv hlOut).1 = rootv))
            (Finmap.insert "split_expr_8"
              (foldRoot hlEvm proofPos (hlEvm.mload proofPos).val 0 idxv hlOut).1
              (Finmap.insert "split_expr_7" hlOut σ))) := by
  -- evm-transported parameter lookups (lookups ignore the evm component)
  have hproofe : ∀ e : EVMState, (Ok e σ)["var_lowLeafProof_mpos"]!! = proofPos :=
    fun _ => hproof
  have hidxle : ∀ e : EVMState, (Ok e σ)["var_lowLeafIndex"]!! = idxv := fun _ => hidxl
  have hroote : ∀ e : EVMState, (Ok e σ)["var_root"]!! = rootv := fun _ => hrootl
  -- the revert-guard is skipped: expr = 0
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', Lit', Var',
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append]
  rw [hexpr]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- split_expr_7 := fun_hashLeaf(var_lowLeaf_mpos)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [hleaf, hhl]
  -- split_expr_8 := fun_calculateRootMemory(proof, index, split_expr_7)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
  rw [hproofe, hidxle]
  rw [calculateRootMemory_call hlt256 hidx hfuel hpath96 hnw hdepthlt]
  -- var := eq(split_expr_8, var_root)
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMEq', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
  rw [hroote]
  simp only [insert_Ok]

/-- **Closed form of `fun_verifyNonInclusion` (success path).**  Given a
well-formed adjacency window (`lowKey < value` and `nextKey = 0 ∨ value <
nextKey`), the function returns `eq(foldRoot(hlEvm, proof, depth, 0, index,
hashLeaf(lowLeaf)), root)` — the absence witness is accepted iff the adjacency
leaf genuinely folds to the authenticated root.  The `fun_hashLeaf` call is
abstracted by `hhl` (pure call: fixed output value and evm effect,
varstore-independent). -/
theorem verifyNonInclusion_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    {rootv val leafPos idxv proofPos : Literal} {v : Identifier}
    {hlEvm : EVMState} {hlOut : Literal}
    (hval : val ≠ 0)
    (hlow : evm.mload leafPos < val)
    (hadj : evm.mload (leafPos + 64) = 0 ∨ val < evm.mload (leafPos + 64))
    (hhl : ∀ σ' : VarStore, execCall (fuel+1) fun_hashLeaf ["split_expr_7"]
        (Ok evm σ', [leafPos]) = Ok hlEvm (σ'.insert "split_expr_7" hlOut))
    (hlt256 : hlEvm.mload proofPos < 256)
    (hidx : idxv < Fin.shiftLeft (1 : UInt256) (hlEvm.mload proofPos))
    (hfuel : 2 * (hlEvm.mload proofPos).val + 2 ≤ fuel)
    (hpath96 : 96 ≤ proofPos.val)
    (hnw : proofPos.val + 32 * (hlEvm.mload proofPos).val + 64 ≤ 2 ^ 256)
    (hdepthlt : (hlEvm.mload proofPos).val < 2 ^ 64) :
    execCall (fuel+1) fun_verifyNonInclusion [v]
        (Ok evm store, [rootv, val, leafPos, idxv, proofPos])
      = Ok (foldRoot hlEvm proofPos (hlEvm.mload proofPos).val 0 idxv hlOut).2
          (store.insert v (fromBool
            ((foldRoot hlEvm proofPos (hlEvm.mload proofPos).val 0 idxv hlOut).1 = rootv))) := by
  unfold execCall call fun_verifyNonInclusion
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  -- initcall facts
  set s0 := (Ok evm store)☎️⟦["var_root", "var_value", "var_lowLeaf_mpos", "var_lowLeafIndex",
      "var_lowLeafProof_mpos"], [rootv, val, leafPos, idxv, proofPos]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have he0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["var_root"]!! = rootv := by rw [hs0]; exact lookup_initcall_1
  have hp2 : s0["var_value"]!! = val := by rw [hs0]; exact lookup_initcall_2 (by decide)
  have hp3 : s0["var_lowLeaf_mpos"]!! = leafPos := by
    rw [hs0]; exact lookup_initcall_3 (by decide) (by decide)
  have hp4 : s0["var_lowLeafIndex"]!! = idxv := by
    rw [hs0]; exact lookup_initcall_4 (by decide) (by decide) (by decide)
  have hp5 : s0["var_lowLeafProof_mpos"]!! = proofPos := by
    rw [hs0]; exact lookup_initcall_5 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by rw [hs0eq, evm_Ok] at he0; exact he0
  subst e0
  rw [hs0eq] at hp1 hp2 hp3 hp4 hp5 ⊢
  -- statement 1: if iszero(var_value) { revert } — skipped (val ≠ 0)
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [hp2]
  rw [show fromBool (val = 0) = (0 : UInt256) from by rw [decide_eq_false hval]; rfl]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- statement 2: _1 := mload(var_lowLeaf_mpos)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMMload', multifill_cons, multifill_nil]
  rw [hp3]
  simp only [evm_Ok, insert_Ok]
  -- statement 3: split_expr_1 := lt(_1, var_value)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin, lookup_insert_ne_fin (by decide), hp2]
  rw [show fromBool (evm.mload leafPos < val) = (1 : UInt256) from by
    rw [decide_eq_true hlow]; rfl]
  simp only [insert_Ok]
  -- statement 4: if iszero(split_expr_1) { revert } — skipped
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- statement 5: split_expr_3 := add(var_lowLeaf_mpos, 64)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMAdd', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hp3]
  simp only [insert_Ok]
  -- statement 6: _2 := mload(split_expr_3)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMMload', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [evm_Ok, insert_Ok]
  -- statement 7: split_expr_4 := iszero(_2)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMIszero', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [insert_Ok]
  -- statement 8: expr := iszero(split_expr_4)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMIszero', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [insert_Ok]
  -- statement 9: the conditional window check — branch on the adjacency shape
  rcases hadj with h0 | hgt
  · -- nextKey = 0: expr = 0, both ifs are skipped
    rw [h0]
    rw [cons, If']
    simp only [evalArgs, evalTail, cons', head', reverse', Lit', Var',
               List.reverse_cons, List.reverse_nil, List.nil_append,
               List.singleton_append]
    rw [lookup_insert_self_fin]
    rw [show fromBool (decide (fromBool (decide True) = 0)) = (0 : UInt256) from by decide]
    rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
    try simp only [overwrite?_of_Ok]
    -- the common tail
    rw [ni_tail (rootv := rootv)
      (by rw [lookup_insert_self_fin])
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact hp3)
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact hp5)
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact hp4)
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact hp1)
      hhl hlt256 hidx hfuel hpath96 hnw hdepthlt]
    -- call wrapper
    try rw [lookup_insert_self_fin]
    try rw [reviveJump_of_isOk' (by trivial)]
    try rw [setStore_ok]
    try simp only [insert_Ok]
    try rfl
  · -- value < nextKey: expr = 1, the inner if runs and resets expr to 0
    have hnz : evm.mload (leafPos + 64) ≠ 0 := by
      intro h
      rw [h] at hgt
      exact absurd hgt (by simp)
    rw [cons, If']
    simp only [evalArgs, evalTail, cons', head', reverse', Lit', Var',
               List.reverse_cons, List.reverse_nil, List.nil_append,
               List.singleton_append]
    rw [lookup_insert_self_fin]
    rw [show fromBool (fromBool (evm.mload (leafPos + 64) = 0) = 0) = (1 : UInt256) from by
      rw [decide_eq_false hnz]; rfl]
    rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
    -- inner window body: split_expr_5 := gt(_2, var_value) ; expr := iszero(split_expr_5)
    rw [window_body
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_self_fin])
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact hp2)
      hgt]
    -- the common tail
    rw [ni_tail (rootv := rootv)
      (by rw [lookup_insert_self_fin])
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact hp3)
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact hp5)
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact hp4)
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact hp1)
      hhl hlt256 hidx hfuel hpath96 hnw hdepthlt]
    -- call wrapper
    try rw [lookup_insert_self_fin]
    try rw [reviveJump_of_isOk' (by trivial)]
    try rw [setStore_ok]
    try simp only [insert_Ok]
    try rfl

/-- **Fully concrete closed form** — `verifyNonInclusion_call` with the
`fun_hashLeaf` step discharged by `hashLeaf_call_acc` (#ported leaf-hash):
the absence witness is accepted iff `foldRoot` of the leaf hash
`hashLeafOut(evm, lowLeaf)` equals the authenticated root. -/
theorem verifyNonInclusion_call_concrete
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    {rootv val leafPos idxv proofPos : Literal} {v : Identifier}
    (hval : val ≠ 0)
    (hlow : evm.mload leafPos < val)
    (hadj : evm.mload (leafPos + 64) = 0 ∨ val < evm.mload (leafPos + 64))
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hlt256 : (hashLeafOut evm leafPos).2.mload proofPos < 256)
    (hidx : idxv < Fin.shiftLeft (1 : UInt256) ((hashLeafOut evm leafPos).2.mload proofPos))
    (hfuel : 2 * ((hashLeafOut evm leafPos).2.mload proofPos).val + 2 ≤ fuel)
    (hpath96 : 96 ≤ proofPos.val)
    (hnw : proofPos.val + 32 * ((hashLeafOut evm leafPos).2.mload proofPos).val + 64 ≤ 2 ^ 256)
    (hdepthlt : ((hashLeafOut evm leafPos).2.mload proofPos).val < 2 ^ 64) :
    execCall (fuel+1) fun_verifyNonInclusion [v]
        (Ok evm store, [rootv, val, leafPos, idxv, proofPos])
      = Ok (foldRoot (hashLeafOut evm leafPos).2 proofPos
            ((hashLeafOut evm leafPos).2.mload proofPos).val 0 idxv
            (hashLeafOut evm leafPos).1).2
          (store.insert v (fromBool
            ((foldRoot (hashLeafOut evm leafPos).2 proofPos
                ((hashLeafOut evm leafPos).2.mload proofPos).val 0 idxv
                (hashLeafOut evm leafPos).1).1 = rootv))) :=
  verifyNonInclusion_call hval hlow hadj
    (fun _ => hashLeaf_call_acc hp) hlt256 hidx hfuel hpath96 hnw hdepthlt

end

end generated.AtomicFlowManager.AtomicFlowManager
