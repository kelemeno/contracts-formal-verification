import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.fun_calculateRootMemory
import specs.AtomicFlowManager.AtomicFlowManager.imt_path_user
import specs.KeccakDeterminism

/-
  TOP-LEVEL closed form of `fun_calculateRootMemory` — lifts `fold_loop`
  (the loop = pure Merkle fold `foldRoot`) past the function's two Solidity
  bound-guards and the initialisers, giving the whole function as `foldRoot`.
  On the success path the prelude leaves the evm UNCHANGED (all mload/lt/shl/eq
  are pure; both guard reverts are skipped), so the loop runs from `Ok evm
  store_pre` and `fold_loop` closes it.
-/

namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism

set_option maxRecDepth 6000
set_option maxHeartbeats 12000000
set_option linter.dupNamespace false

private lemma insert_Ok'' {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

private lemma evm_Ok {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

private lemma reviveJump_of_isOk' {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok'']; exact lookup_insert_of_ne h

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok'']; exact lookup_insert' (by trivial)

/-- **Top-level closed form of `fun_calculateRootMemory`.** -/
lemma calculateRootMemory_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    {path idx leaf : Literal} {v : Identifier}
    (hlt256 : evm.mload path < 256)
    (hidx : idx < Fin.shiftLeft (1 : UInt256) (evm.mload path))
    (hfuel : 2 * (evm.mload path).val + 2 ≤ fuel)
    (hpath96 : 96 ≤ path.val)
    (hnw : path.val + 32 * (evm.mload path).val + 64 ≤ 2 ^ 256)
    (hdepthlt : (evm.mload path).val < 2 ^ 64) :
    execCall (fuel+1) fun_calculateRootMemory [v] (Ok evm store, [path, idx, leaf])
      = Ok (foldRoot evm path (evm.mload path).val 0 idx leaf).2
          (store.insert v (foldRoot evm path (evm.mload path).val 0 idx leaf).1) := by
  unfold execCall call fun_calculateRootMemory
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  -- initcall facts
  set s0 := (Ok evm store)☎️⟦["var_path_mpos", "var_index", "var_itemHash"], [path, idx, leaf]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have he0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["var_path_mpos"]!! = path := by rw [hs0]; exact lookup_initcall_1
  have hp2 : s0["var_index"]!! = idx := by rw [hs0]; exact lookup_initcall_2 (by decide)
  have hp3 : s0["var_itemHash"]!! = leaf := by rw [hs0]; exact lookup_initcall_3 (by decide) (by decide)
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by rw [hs0eq, evm_Ok] at he0; exact he0
  subst e0
  rw [hs0eq] at hp1 hp2 hp3 ⊢
  -- statement 1: expr := mload(var_path_mpos)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMMload', multifill_cons, multifill_nil]
  rw [hp1]
  simp only [evm_Ok]
  -- abbreviations
  have hokσ : isOk (Ok evm σ0) := trivial
  -- statement 2: split_expr_0 := lt(expr, 256)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert]
  -- statement 3: if iszero(split_expr_0) { revert } — skipped
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [lookup_insert' (by simp only [isOk_insert]; trivial)]
  rw [show fromBool (evm.mload path < 256) = (1 : UInt256) from by rw [decide_eq_true hlt256]; rfl]
  simp only [head', List.head!]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  simp only [overwrite?_of_Ok]
  -- statement 4: split_expr_2 := shl(expr, 1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMShl', multifill_cons, multifill_nil]
  rw [lookup_insert_of_ne (by decide), lookup_insert]
  -- statement 5: split_expr_3 := lt(var_index, split_expr_2)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  -- split_expr_2 lookup (same-var top, nested base): lookup_insert'
  rw [lookup_insert' (by simp only [isOk_insert]; trivial)]
  -- var_index lookup: 3 skips to σ0, then hp2
  rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
      lookup_insert_of_ne (by decide), hp2]
  -- statement 6: if iszero(split_expr_3) { revert } — skipped (idx < 2^depth)
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [lookup_insert' (by simp only [isOk_insert]; trivial)]
  rw [show fromBool (idx < Fin.shiftLeft (1 : UInt256) (evm.mload path)) = (1 : UInt256) from by
    rw [decide_eq_true hidx]; rfl]
  try simp only [head', List.head!]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- statement 7: let var_currentHash := var_itemHash
  rw [cons, LetEq']
  simp only [Var']
  rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
      lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide), hp3]
  -- statements 8-9: let var_i := 0 ; var_i := 0
  rw [cons, LetEq']
  simp only [Lit']
  rw [cons, Assign']
  simp only [Lit', eval]
  -- statement 10: the For loop — fold the inline AST into the named Common defs
  rw [cons]
  rw [show (PrimCall P.Lt [Var "var_i", Var "expr"])
        = _root_.AtomicFlowManager.Common.for_456069591477598358_cond from rfl,
      show ([AssignPrimCall ["var_i"] P.Add [Var "var_i", Lit 1]])
        = _root_.AtomicFlowManager.Common.for_456069591477598358_post from rfl,
      show ([LetCall ["split_expr_5"] mod_uint256 [Var "var_index"],
             LetPrimCall ["expr_1"] P.Iszero [Var "split_expr_5"],
             LetEq "expr_2" (Lit 0),
             Switch (Var "expr_1")
               [(0, [LetCall ["split_expr_6"] memory_array_index_access_struct_InteropCall_dyn
                       [Var "var_path_mpos", Var "var_i"],
                     LetPrimCall ["split_expr_7"] P.Mload [Var "split_expr_6"],
                     AssignCall ["expr_2"] fun_efficientHash
                       [Var "split_expr_7", Var "var_currentHash"]])]
               [LetCall ["split_expr_8"] memory_array_index_access_struct_InteropCall_dyn
                  [Var "var_path_mpos", Var "var_i"],
                LetPrimCall ["split_expr_9"] P.Mload [Var "split_expr_8"],
                AssignCall ["expr_2"] fun_efficientHash
                  [Var "var_currentHash", Var "split_expr_9"]],
             Assign "var_currentHash" (Var "expr_2"),
             AssignCall ["var_index"] checked_div_uint256 [Var "var_index"]])
        = _root_.AtomicFlowManager.Common.for_456069591477598358_body from rfl]
  -- collapse the pre-For state tower to a single Ok
  simp only [insert_Ok'']
  -- apply the loop closed form
  obtain ⟨σ', hσ'eq, hσ'cur⟩ := fold_loop
    (k := (evm.mload path).val) (fuel := fuel+1) (evm := evm)
    (store := ((((((σ0.insert "expr" (evm.mload path)).insert "split_expr_0" 1).insert
      "split_expr_2" (Fin.shiftLeft 1 (evm.mload path))).insert "split_expr_3" 1).insert
      "var_currentHash" leaf).insert "var_i" 0).insert "var_i" 0)
    (path := path) (idx := idx) (cur := leaf) (iv := 0) (Ln := evm.mload path)
    (lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hp2)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hp1)
    (by rw [show ((0 : UInt256)).val = 0 from by decide]; omega)
    rfl (by omega) hpath96 hnw hdepthlt
  rw [hσ'eq]
  -- final statement: var := var_currentHash
  rw [cons, nil, Assign']
  simp only [Var']
  rw [hσ'cur]
  -- call wrapper: reduce the return-value lookup, then 🧟 / 🏪 / ⟦v↦·⟧
  rw [lookup_insert]
  rw [reviveJump_of_isOk' (by simp only [isOk_insert]; trivial)]
  rw [insert_Ok'']
  rw [setStore_ok]
  rw [insert_Ok'']

end

end generated.AtomicFlowManager.AtomicFlowManager
