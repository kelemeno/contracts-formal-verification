import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.fun_efficientHash
import generated.AtomicFlowManager.AtomicFlowManager.mod_uint256
import generated.AtomicFlowManager.AtomicFlowManager.checked_div_uint256
import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.Common.for_456069591477598358

import specs.KeccakDeterminism

/-
  MERKLE PATH FOLD — building blocks for `fun_calculateRootMemory`
  (the root recomputation used by `AtomicInteropProof.verifyInclusion` /
  `verifyNonInclusion` / `verifyTimeoutAdjacency`).

  The fold's loop body per level `i`:
      parity := index & 1;  sibling := mload(path[i]);
      current := parity == 0 ? H(current, sibling) : H(sibling, current);
      index := index >> 1
  This file provides the closed forms of the per-iteration helpers:
  `mod_uint256` (`x & 1`), `checked_div_uint256` (`x >> 1`),
  `memory_array_index_access…` (bounds-checked `base + 32*i + 32`), and this
  contract's copy of the pair hash `fun_efficientHash` (one `accOut` step).
  The loop invariant / full fold closed form builds on these.

  Axiom-free (`[propext, Quot.sound, Classical.choice]`).
-/

namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism

set_option maxRecDepth 6000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

private lemma insert_Ok' {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

private lemma evm_setEvm_of_isOk' {s : State} {e : EVMState} (h : isOk s) :
    (s.setEvm e).evm = e := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma reviveJump_of_isOk' {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma lookup_setEvm_of_isOk' {s : State} {e : EVMState} {k : Identifier}
    (h : isOk s) : (s.setEvm e)[k]!! = s[k]!! := by
  obtain ⟨evm₀, st, rfl⟩ := State_of_isOk h; rfl

private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok']; exact lookup_insert_of_ne h

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok']; exact lookup_insert' (by trivial)

private lemma lookup_ok_evm {e e' : EVMState} {σ : VarStore} {k : Identifier} :
    (Ok e σ)[k]!! = (Ok e' σ)[k]!! := rfl

private lemma primCall_keccakOut' {s : State} {a b : Literal} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (keccakOut s.evm a b).2, [(keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

/-- Closed form of this contract's Merkle pair hash (same body as the
commitment tree's copy): one `accOut` step at `(lhs, rhs)`. -/
lemma efficientHash_call_acc
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {lhs rhs : Literal} {v : Identifier} :
    execCall (fuel+1) fun_efficientHash [v] (Ok evm store, [lhs, rhs])
      = Ok (accOut evm lhs rhs).2 (store.insert v (accOut evm lhs rhs).1) := by
  unfold execCall call fun_efficientHash
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, nil]
  simp only [ExprStmtPrimCall', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMstore']
  simp only [multifill', multifill_nil, multifill_cons, overwrite?_of_Ok]
  rw [primCall_keccakOut']
  have hok₀ : isOk ((Ok evm store)☎️⟦["var_lhs", "var_rhs"], [lhs, rhs]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm₀ : ((Ok evm store)☎️⟦["var_lhs", "var_rhs"], [lhs, rhs]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hlhs : ((Ok evm store)☎️⟦["var_lhs", "var_rhs"], [lhs, rhs]⟧)["var_lhs"]!! = lhs :=
    lookup_initcall_1
  have hrhs : ((Ok evm store)☎️⟦["var_lhs", "var_rhs"], [lhs, rhs]⟧)["var_rhs"]!! = rhs :=
    lookup_initcall_2 (by decide)
  set s₀ := (Ok evm store)☎️⟦["var_lhs", "var_rhs"], [lhs, rhs]⟧ with hs₀
  set s₁ := s₀🇪⟦s₀.evm.mstore 0 (s₀["var_lhs"]!!)⟧ with hs₁
  have hs₁_ok : isOk s₁ := by rw [hs₁, isOk_setEvm]; exact hok₀
  set host := s₁🇪⟦s₁.evm.mstore 32 (s₁["var_rhs"]!!)⟧ with hhost
  have hhost_ok : isOk host := by rw [hhost, isOk_setEvm]; exact hs₁_ok
  have hhost_evm : host.evm = (evm.mstore 0 lhs).mstore 32 rhs := by
    rw [hhost, evm_setEvm_of_isOk' hs₁_ok, hs₁, evm_setEvm_of_isOk' hok₀, hevm₀, hlhs,
        lookup_setEvm_of_isOk' hok₀, hrhs]
  rw [hhost_evm]
  unfold accOut
  generalize hout : keccakOut ((evm.mstore 0 lhs).mstore 32 rhs) 0 64 = out
  simp only [multifill_cons, multifill_nil]
  have hsetEvm_ok : isOk (host.setEvm out.2) := by
    rw [isOk_setEvm]; exact hhost_ok
  have hin_ok : isOk ((host.setEvm out.2)⟦"var_result" ↦ out.1⟧) := by
    rw [isOk_insert]; exact hsetEvm_ok
  rw [lookup_insert' hsetEvm_ok]
  rw [reviveJump_of_isOk' hin_ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = out.2 := by
    have h := congrArg State.evm hi
    rw [evm_insert, evm_setEvm_of_isOk' hhost_ok] at h
    exact h.symm
  rw [hi, setStore_ok]
  simp only [insert_Ok']
  rw [hi_evm]

/-- Closed form of `mod_uint256(x)`: pure, returns `x & 1` (the path parity). -/
lemma mod2_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x : Literal} {v : Identifier} :
    execCall (fuel+1) mod_uint256 [v] (Ok evm store, [x])
      = (Ok evm store)⟦v ↦ Fin.land x 1⟧ := by
  unfold execCall call mod_uint256
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  simp only [cons, nil]
  simp only [LetEq', Assign', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMAnd']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["x"], [x]⟧) := isOk_initcall_of_isOk trivial
  have hx : ((Ok evm store)☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧⟦"_1" ↦ 0⟧)["x"]!! = x := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact lookup_initcall_1
  rw [hx]
  have hok2 : isOk ((Ok evm store)☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧⟦"_1" ↦ 0⟧) := by
    rw [isOk_insert, isOk_insert]; exact hok0
  have hin_ok : isOk ((Ok evm store)☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧⟦"_1" ↦ 0⟧⟦"r" ↦ Fin.land x 1⟧) := by
    rw [isOk_insert]; exact hok2
  rw [lookup_insert' hok2]
  rw [reviveJump_of_isOk' hin_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = evm := by
    have h := congrArg State.evm hi
    simp only [evm_insert] at h
    rw [show ((Ok evm store)☎️⟦["x"], [x]⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]

/-- Closed form of `checked_div_uint256(x)`: pure, returns `x >> 1`. -/
lemma div2_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x : Literal} {v : Identifier} :
    execCall (fuel+1) checked_div_uint256 [v] (Ok evm store, [x])
      = (Ok evm store)⟦v ↦ Fin.shiftRight x 1⟧ := by
  unfold execCall call checked_div_uint256
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  simp only [cons, nil]
  simp only [LetEq', Assign', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMShr']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["x"], [x]⟧) := isOk_initcall_of_isOk trivial
  have hx : ((Ok evm store)☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧⟦"_1" ↦ 0⟧)["x"]!! = x := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact lookup_initcall_1
  rw [hx]
  have hok2 : isOk ((Ok evm store)☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧⟦"_1" ↦ 0⟧) := by
    rw [isOk_insert, isOk_insert]; exact hok0
  have hin_ok : isOk ((Ok evm store)☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧⟦"_1" ↦ 0⟧⟦"r" ↦ Fin.shiftRight x 1⟧) := by
    rw [isOk_insert]; exact hok2
  rw [lookup_insert' hok2]
  rw [reviveJump_of_isOk' hin_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = evm := by
    have h := congrArg State.evm hi
    simp only [evm_insert] at h
    rw [show ((Ok evm store)☎️⟦["x"], [x]⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]

/-- Closed form of the path-array element access (in-bounds case): pure,
returns `base + 32*i + 32`. -/
lemma array_index_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {base idx : Literal} {v : Identifier}
    (hbound : idx < evm.mload base) :
    execCall (fuel+1) memory_array_index_access_struct_InteropCall_dyn [v]
        (Ok evm store, [base, idx])
      = (Ok evm store)⟦v ↦ (base + Fin.shiftLeft idx 5) + 32⟧ := by
  unfold execCall call memory_array_index_access_struct_InteropCall_dyn
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMload', EVMLt', EVMShl', EVMAdd']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hbase : ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧)["baseRef"]!! = base :=
    lookup_initcall_1
  rw [hevm0, hbase]
  have hok1 : isOk ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧⟦"split_expr_0" ↦ evm.mload base⟧) :=
    isOk_insert.mpr hok0
  have hidx : ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧⟦"split_expr_0" ↦ evm.mload base⟧)["index"]!!
      = idx := by
    rw [lookup_insert_of_ne (by decide)]
    exact lookup_initcall_2 (by decide)
  have hs0 : ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧⟦"split_expr_0" ↦ evm.mload base⟧)["split_expr_0"]!!
      = evm.mload base := lookup_insert' hok0
  rw [hidx, hs0]
  -- the bounds guard passes
  rw [show fromBool (idx < evm.mload base) = (1 : UInt256) from by
    rw [decide_eq_true hbound]; rfl]
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append] <;> skip
  have hok2 : isOk ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧⟦"split_expr_0" ↦ evm.mload base⟧⟦"split_expr_1" ↦ 1⟧) :=
    isOk_insert.mpr hok1
  have hs1 : ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧⟦"split_expr_0" ↦ evm.mload base⟧⟦"split_expr_1" ↦ 1⟧)["split_expr_1"]!!
      = 1 := lookup_insert' hok1
  rw [hs1, EVMIszero']
  simp only [head', List.head!]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) by decide]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  -- addr computation
  have hidx2 : ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧⟦"split_expr_0" ↦ evm.mload base⟧⟦"split_expr_1" ↦ 1⟧)["index"]!!
      = idx := by
    rw [lookup_insert_of_ne (by decide)]
    exact hidx
  rw [hidx2]
  have hok3 : isOk ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧⟦"split_expr_0" ↦ evm.mload base⟧⟦"split_expr_1" ↦ 1⟧⟦"split_expr_2" ↦ Fin.shiftLeft idx 5⟧) :=
    isOk_insert.mpr hok2
  have hbase2 : ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧⟦"split_expr_0" ↦ evm.mload base⟧⟦"split_expr_1" ↦ 1⟧⟦"split_expr_2" ↦ Fin.shiftLeft idx 5⟧)["baseRef"]!!
      = base := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
        lookup_insert_of_ne (by decide)]
    exact hbase
  have hs2 : ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧⟦"split_expr_0" ↦ evm.mload base⟧⟦"split_expr_1" ↦ 1⟧⟦"split_expr_2" ↦ Fin.shiftLeft idx 5⟧)["split_expr_2"]!!
      = Fin.shiftLeft idx 5 := lookup_insert' hok2
  rw [hbase2, hs2]
  have hok4 : isOk ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧⟦"split_expr_0" ↦ evm.mload base⟧⟦"split_expr_1" ↦ 1⟧⟦"split_expr_2" ↦ Fin.shiftLeft idx 5⟧⟦"split_expr_3" ↦ base + Fin.shiftLeft idx 5⟧) :=
    isOk_insert.mpr hok3
  have hs3 : ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧⟦"split_expr_0" ↦ evm.mload base⟧⟦"split_expr_1" ↦ 1⟧⟦"split_expr_2" ↦ Fin.shiftLeft idx 5⟧⟦"split_expr_3" ↦ base + Fin.shiftLeft idx 5⟧)["split_expr_3"]!!
      = base + Fin.shiftLeft idx 5 := lookup_insert' hok3
  rw [hs3]
  have hin_ok : isOk ((Ok evm store)☎️⟦["baseRef", "index"], [base, idx]⟧⟦"split_expr_0" ↦ evm.mload base⟧⟦"split_expr_1" ↦ 1⟧⟦"split_expr_2" ↦ Fin.shiftLeft idx 5⟧⟦"split_expr_3" ↦ base + Fin.shiftLeft idx 5⟧⟦"addr" ↦ (base + Fin.shiftLeft idx 5) + 32⟧) :=
    isOk_insert.mpr hok4
  rw [lookup_insert' hok4]
  rw [reviveJump_of_isOk' hin_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = evm := by
    have h := congrArg State.evm hi
    simp only [evm_insert] at h
    rw [hevm0] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]

open AtomicFlowManager.Common in
/-- The sibling read by fold level `i`: `mload(path + 32*i + 32)`. -/
def foldSib (evm : EVMState) (path i : UInt256) : UInt256 :=
  evm.mload ((path + Fin.shiftLeft i 5) + 32)

open AtomicFlowManager.Common in
set_option maxHeartbeats 8000000 in
/-- **Fold body, odd level** (`index & 1 ≠ 0`): the current node is a right
child, so the level hashes `H(sibling, current)`; the index halves. -/
lemma fold_body_odd
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {idx path i cur : Literal}
    (hidx : (Ok evm store)["var_index"]!! = idx)
    (hpath : (Ok evm store)["var_path_mpos"]!! = path)
    (hi : (Ok evm store)["var_i"]!! = i)
    (hcur : (Ok evm store)["var_currentHash"]!! = cur)
    (hbound : i < evm.mload path)
    (hodd : Fin.land idx 1 ≠ 0) :
    exec (fuel+1) (.Block for_456069591477598358_body) (Ok evm store)
      = Ok (accOut evm (foldSib evm path i) cur).2
          ((((((((store.insert "split_expr_5" (Fin.land idx 1)).insert
            "expr_1" 0).insert "expr_2" 0).insert
            "split_expr_6" ((path + Fin.shiftLeft i 5) + 32)).insert
            "split_expr_7" (foldSib evm path i)).insert
            "expr_2" (accOut evm (foldSib evm path i) cur).1).insert
            "var_currentHash" (accOut evm (foldSib evm path i) cur).1).insert
            "var_index" (Fin.shiftRight idx 1)) := by
  unfold _root_.AtomicFlowManager.Common.for_456069591477598358_body
  simp only [cons, nil]
  -- statement 1: split_expr_5 := mod_uint256(var_index)
  rw [LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append]
  rw [hidx, mod2_call]
  simp only [insert_Ok']
  -- statement 2: expr_1 := iszero(split_expr_5)  (= 0, odd index)
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMIszero', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [show fromBool (Fin.land idx 1 = 0) = (0 : UInt256) from by
    rw [decide_eq_false hodd]; rfl]
  simp only [insert_Ok']
  -- statement 3: expr_2 := 0
  rw [LetEq']
  simp only [Lit', insert_Ok']
  -- the switch: scrutinee = expr_1 = 0 → the case-0 branch is selected
  rw [Switch']
  simp only [Var', execSwitchCases, List.foldr]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  -- the scrutinee is 0 = the case value: select the case-0 branch, discard default
  simp only [if_true]
  -- reduce the case-0 branch body
  simp only [cons, nil]
  rw [LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append, multifill_cons, multifill_nil]
  have hpath3 : (Ok evm (Finmap.insert "expr_2" 0 (Finmap.insert "expr_1" 0
      (Finmap.insert "split_expr_5" (Fin.land idx 1) store))))["var_path_mpos"]!! = path := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide)]
    exact hpath
  have hi3 : (Ok evm (Finmap.insert "expr_2" 0 (Finmap.insert "expr_1" 0
      (Finmap.insert "split_expr_5" (Fin.land idx 1) store))))["var_i"]!! = i := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide)]
    exact hi
  rw [hpath3, hi3, array_index_call hbound]
  simp only [insert_Ok']
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMMload', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  simp only [insert_Ok']
  simp only [AssignCall', Assign', evalArgs, evalTail, cons', head', reverse',
             multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil]
  have hs7 : (Ok evm (Finmap.insert "split_expr_7" (evm.mload (path + Fin.shiftLeft i 5 + 32))
      (Finmap.insert "split_expr_6" (path + Fin.shiftLeft i 5 + 32)
      (Finmap.insert "expr_2" 0 (Finmap.insert "expr_1" 0
      (Finmap.insert "split_expr_5" (Fin.land idx 1) store))))))["split_expr_7"]!!
      = evm.mload (path + Fin.shiftLeft i 5 + 32) := lookup_insert_self_fin
  have hcur5 : (Ok evm (Finmap.insert "split_expr_7" (evm.mload (path + Fin.shiftLeft i 5 + 32))
      (Finmap.insert "split_expr_6" (path + Fin.shiftLeft i 5 + 32)
      (Finmap.insert "expr_2" 0 (Finmap.insert "expr_1" 0
      (Finmap.insert "split_expr_5" (Fin.land idx 1) store))))))["var_currentHash"]!! = cur := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide)]
    exact hcur
  rw [hs7, hcur5, efficientHash_call_acc]
  simp only [insert_Ok']
  -- var_currentHash := expr_2
  have he2 : (Ok (accOut evm (evm.mload (path + Fin.shiftLeft i 5 + 32)) cur).2
      (Finmap.insert "expr_2" (accOut evm (evm.mload (path + Fin.shiftLeft i 5 + 32)) cur).1
        (Finmap.insert "split_expr_7" (evm.mload (path + Fin.shiftLeft i 5 + 32))
          (Finmap.insert "split_expr_6" (path + Fin.shiftLeft i 5 + 32)
            (Finmap.insert "expr_2" 0
              (Finmap.insert "expr_1" 0
                (Finmap.insert "split_expr_5" (Fin.land idx 1) store)))))))["expr_2"]!!
      = (accOut evm (evm.mload (path + Fin.shiftLeft i 5 + 32)) cur).1 :=
    lookup_insert_self_fin
  rw [he2]
  -- var_index := checked_div_uint256(var_index)
  have hidx7 : (Ok (accOut evm (evm.mload (path + Fin.shiftLeft i 5 + 32)) cur).2
      (Finmap.insert "var_currentHash" (accOut evm (evm.mload (path + Fin.shiftLeft i 5 + 32)) cur).1
        (Finmap.insert "expr_2" (accOut evm (evm.mload (path + Fin.shiftLeft i 5 + 32)) cur).1
          (Finmap.insert "split_expr_7" (evm.mload (path + Fin.shiftLeft i 5 + 32))
            (Finmap.insert "split_expr_6" (path + Fin.shiftLeft i 5 + 32)
              (Finmap.insert "expr_2" 0
                (Finmap.insert "expr_1" 0
                  (Finmap.insert "split_expr_5" (Fin.land idx 1) store))))))))["var_index"]!!
      = idx := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide)]
    exact hidx
  rw [hidx7, div2_call]
  simp only [insert_Ok']
  unfold foldSib
  rfl

open AtomicFlowManager.Common in
set_option maxHeartbeats 8000000 in
/-- **Fold body, even level** (`index & 1 = 0`): the current node is a left
child, so the level hashes `H(current, sibling)`; the index halves. -/
lemma fold_body_even
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {idx path i cur : Literal}
    (hidx : (Ok evm store)["var_index"]!! = idx)
    (hpath : (Ok evm store)["var_path_mpos"]!! = path)
    (hi : (Ok evm store)["var_i"]!! = i)
    (hcur : (Ok evm store)["var_currentHash"]!! = cur)
    (hbound : i < evm.mload path)
    (heven : Fin.land idx 1 = 0) :
    exec (fuel+1) (.Block for_456069591477598358_body) (Ok evm store)
      = Ok (accOut evm cur (foldSib evm path i)).2
          ((((((((store.insert "split_expr_5" (Fin.land idx 1)).insert
            "expr_1" 1).insert "expr_2" 0).insert
            "split_expr_8" ((path + Fin.shiftLeft i 5) + 32)).insert
            "split_expr_9" (foldSib evm path i)).insert
            "expr_2" (accOut evm cur (foldSib evm path i)).1).insert
            "var_currentHash" (accOut evm cur (foldSib evm path i)).1).insert
            "var_index" (Fin.shiftRight idx 1)) := by
  unfold _root_.AtomicFlowManager.Common.for_456069591477598358_body
  simp only [cons, nil]
  -- statement 1: split_expr_5 := mod_uint256(var_index)
  rw [LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append]
  rw [hidx, mod2_call]
  simp only [insert_Ok']
  -- statement 2: expr_1 := iszero(split_expr_5)  (= 1, even index)
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMIszero', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [show fromBool (Fin.land idx 1 = 0) = (1 : UInt256) from by
    rw [decide_eq_true heven]; rfl]
  simp only [insert_Ok']
  -- statement 3: expr_2 := 0
  rw [LetEq']
  simp only [Lit', insert_Ok']
  -- the switch: scrutinee = expr_1 = 1 ≠ 0 (the case value): the DEFAULT runs
  rw [Switch']
  simp only [Var', execSwitchCases, List.foldr]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [if_neg (by decide : ¬ ((0 : UInt256) = 1))]
  -- reduce the default branch body
  simp only [cons, nil]
  rw [LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append, multifill_cons, multifill_nil]
  have hpath3 : (Ok evm (Finmap.insert "expr_2" 0 (Finmap.insert "expr_1" 1
      (Finmap.insert "split_expr_5" (Fin.land idx 1) store))))["var_path_mpos"]!! = path := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide)]
    exact hpath
  have hi3 : (Ok evm (Finmap.insert "expr_2" 0 (Finmap.insert "expr_1" 1
      (Finmap.insert "split_expr_5" (Fin.land idx 1) store))))["var_i"]!! = i := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide)]
    exact hi
  rw [hpath3, hi3, array_index_call hbound]
  simp only [insert_Ok']
  rw [LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMMload', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  simp only [insert_Ok']
  simp only [AssignCall', Assign', evalArgs, evalTail, cons', head', reverse',
             multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil]
  have hs9 : (Ok evm (Finmap.insert "split_expr_9" (evm.mload (path + Fin.shiftLeft i 5 + 32))
      (Finmap.insert "split_expr_8" (path + Fin.shiftLeft i 5 + 32)
      (Finmap.insert "expr_2" 0 (Finmap.insert "expr_1" 1
      (Finmap.insert "split_expr_5" (Fin.land idx 1) store))))))["split_expr_9"]!!
      = evm.mload (path + Fin.shiftLeft i 5 + 32) := lookup_insert_self_fin
  have hcur5 : (Ok evm (Finmap.insert "split_expr_9" (evm.mload (path + Fin.shiftLeft i 5 + 32))
      (Finmap.insert "split_expr_8" (path + Fin.shiftLeft i 5 + 32)
      (Finmap.insert "expr_2" 0 (Finmap.insert "expr_1" 1
      (Finmap.insert "split_expr_5" (Fin.land idx 1) store))))))["var_currentHash"]!! = cur := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide)]
    exact hcur
  rw [hs9, hcur5, efficientHash_call_acc]
  simp only [insert_Ok']
  -- var_currentHash := expr_2
  have he2 : (Ok (accOut evm cur (evm.mload (path + Fin.shiftLeft i 5 + 32))).2
      (Finmap.insert "expr_2" (accOut evm cur (evm.mload (path + Fin.shiftLeft i 5 + 32))).1
        (Finmap.insert "split_expr_9" (evm.mload (path + Fin.shiftLeft i 5 + 32))
          (Finmap.insert "split_expr_8" (path + Fin.shiftLeft i 5 + 32)
            (Finmap.insert "expr_2" 0
              (Finmap.insert "expr_1" 1
                (Finmap.insert "split_expr_5" (Fin.land idx 1) store)))))))["expr_2"]!!
      = (accOut evm cur (evm.mload (path + Fin.shiftLeft i 5 + 32))).1 :=
    lookup_insert_self_fin
  rw [he2]
  -- var_index := checked_div_uint256(var_index)
  have hidx7 : (Ok (accOut evm cur (evm.mload (path + Fin.shiftLeft i 5 + 32))).2
      (Finmap.insert "var_currentHash" (accOut evm cur (evm.mload (path + Fin.shiftLeft i 5 + 32))).1
        (Finmap.insert "expr_2" (accOut evm cur (evm.mload (path + Fin.shiftLeft i 5 + 32))).1
          (Finmap.insert "split_expr_9" (evm.mload (path + Fin.shiftLeft i 5 + 32))
            (Finmap.insert "split_expr_8" (path + Fin.shiftLeft i 5 + 32)
              (Finmap.insert "expr_2" 0
                (Finmap.insert "expr_1" 1
                  (Finmap.insert "split_expr_5" (Fin.land idx 1) store))))))))["var_index"]!!
      = idx := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide)]
    exact hidx
  rw [hidx7, div2_call]
  simp only [insert_Ok']
  unfold foldSib
  rfl

/-- **The pure Merkle fold.** `foldRoot σ path k i idx cur` folds `k` levels of
the path starting at level `i`: each level reads the sibling from the (frame-
preserved) path array, hashes left/right by the index parity via `accOut`, and
halves the index — the specification of `fun_calculateRootMemory`'s loop. -/
def foldRoot (σ : EVMState) (path : UInt256) :
    ℕ → UInt256 → UInt256 → UInt256 → UInt256 × EVMState
  | 0, _i, _idx, cur => (cur, σ)
  | (k+1), i, idx, cur =>
      let sib := σ.mload ((path + Fin.shiftLeft i 5) + 32)
      let out := if Fin.land idx 1 = 0 then accOut σ cur sib else accOut σ sib cur
      foldRoot out.2 path k (i + 1) (Fin.shiftRight idx 1) out.1

private lemma val_succ {a : UInt256} (h : a.val + 1 < 2 ^ 256) :
    (a + (1 : UInt256)).val = a.val + 1 := by
  have h1v : ((1 : UInt256)).val = 1 := by decide
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  rw [Fin.val_add, h1v]
  exact Nat.mod_eq_of_lt (by omega)

open AtomicFlowManager.Common in
set_option maxHeartbeats 8000000 in
/-- **The fold-loop closed form (M3).** Executing the fold loop with `k`
iterations remaining (`var_i + k = expr`, the path length) computes exactly
`foldRoot`: the final evm is the fold's keccak-advanced evm, and
`var_currentHash` holds the folded root.  Hypotheses: the five loop variables
bound in the store; the loop bound is the path length; the path array lives
above the scratch (`96 ≤ path`) and does not wrap; the length is small; and
fuel covers the iterations (2 per level + 2). -/
lemma fold_loop
    {k : ℕ} {fuel : ℕ} {evm : EVMState} {store : VarStore}
    {path idx cur iv Ln : Literal}
    (hi : (Ok evm store)["var_i"]!! = iv)
    (hLn : (Ok evm store)["expr"]!! = Ln)
    (hidx : (Ok evm store)["var_index"]!! = idx)
    (hcur : (Ok evm store)["var_currentHash"]!! = cur)
    (hpath : (Ok evm store)["var_path_mpos"]!! = path)
    (hk : iv.val + k = Ln.val)
    (hLn_mem : Ln = evm.mload path)
    (hfuel : 2 * k + 2 ≤ fuel)
    (hpath96 : 96 ≤ path.val)
    (hnw : path.val + 32 * Ln.val + 64 ≤ 2 ^ 256)
    (hLnlt : Ln.val < 2 ^ 64) :
    ∃ σ' : VarStore,
      exec fuel (.For for_456069591477598358_cond for_456069591477598358_post
          for_456069591477598358_body) (Ok evm store)
        = Ok (foldRoot evm path k iv idx cur).2 σ'
      ∧ (Ok (foldRoot evm path k iv idx cur).2 σ')["var_currentHash"]!!
          = (foldRoot evm path k iv idx cur).1 := by
  induction k generalizing fuel evm store idx cur iv with
  | zero =>
    -- var_i = expr: the guard is 0, the loop exits immediately
    rcases fuel with _ | _ | f
    · omega
    · omega
    have hiv_eq : iv = Ln := by
      apply Fin.ext; omega
    refine ⟨store, ?_, ?_⟩
    · rw [For']
      dsimp only
      unfold _root_.AtomicFlowManager.Common.for_456069591477598358_cond
      simp only [eval, evalArgs, evalTail, cons', head', reverse', multifill',
                 PrimCall', Lit', Var', execPrimCall, evalPrimCall,
                 List.reverse_cons, List.reverse_nil, List.nil_append,
                 List.singleton_append, EVMLt', mkOk_of_isOk (show isOk (Ok evm store) from trivial)]
      rw [hi, hLn]
      rw [show fromBool (iv < Ln) = (0 : UInt256) from by
        rw [decide_eq_false (by rw [hiv_eq]; exact lt_irrefl Ln)]; rfl]
      simp only [head', List.head!, if_true]
      simp only [overwrite?_of_Ok]
      rfl
    · simpa [foldRoot] using hcur
  | succ k ih =>
    -- expose three fuel units: outer For runs its inner steps at `fb+1`
    obtain ⟨fb, rfl⟩ : ∃ fb, fuel = fb + 1 + 1 + 1 := ⟨fuel - 3, by omega⟩
    -- the level is in-bounds (from the loop variant)
    have hivLn : iv.val < Ln.val := by omega
    have hiv_lt : iv < Ln := by rw [Fin.lt_def]; exact hivLn
    have hLn_evm : Ln = evm.mload path := hLn_mem
    -- === unfold one For iteration and evaluate the guard (= 1) ===
    rw [For']
    dsimp only
    unfold _root_.AtomicFlowManager.Common.for_456069591477598358_cond
    simp only [eval, evalArgs, evalTail, cons', head', reverse', multifill',
               PrimCall', Lit', Var', execPrimCall, evalPrimCall,
               List.reverse_cons, List.reverse_nil, List.nil_append,
               List.singleton_append, EVMLt',
               mkOk_of_isOk (show isOk (Ok evm store) from trivial)]
    rw [hi, hLn]
    rw [show fromBool (iv < Ln) = (1 : UInt256) from by
      rw [decide_eq_true hiv_lt]; rfl]
    simp only [head', List.head!]
    rw [if_neg (by decide : ¬ ((1 : UInt256) = 0))]
    -- === run the body (one fold level) by parity ===
    -- the body sibling and hashed value
    set sib := evm.mload ((path + Fin.shiftLeft iv 5) + 32) with hsib
    -- one accOut step, matching foldRoot's step
    set out := (if Fin.land idx 1 = 0 then accOut evm cur sib else accOut evm sib cur) with hout
    -- prove: exec (fb+1) (Block body) (Ok evm store) = Ok out.2 <bodyStore>, for the parity at hand
    have hbody :
        ∃ bs : VarStore,
          exec (fb+1) (.Block for_456069591477598358_body) (Ok evm store) = Ok out.2 bs
          ∧ (Ok out.2 bs)["var_i"]!! = iv
          ∧ (Ok out.2 bs)["expr"]!! = Ln
          ∧ (Ok out.2 bs)["var_index"]!! = Fin.shiftRight idx 1
          ∧ (Ok out.2 bs)["var_currentHash"]!! = out.1
          ∧ (Ok out.2 bs)["var_path_mpos"]!! = path := by
      obtain ⟨fbb, rfl⟩ : ∃ fbb, fb = fbb + 1 := ⟨fb - 1, by omega⟩
      have hsibfold : sib = foldSib evm path iv := rfl
      by_cases hpar : Fin.land idx 1 = 0
      · -- even: H(current, sibling)
        have hout_eq : out = accOut evm cur (foldSib evm path iv) := by
          rw [hout, if_pos hpar, hsibfold]
        rw [hout_eq]
        rw [fold_body_even hidx hpath hi hcur (by rw [← hLn_evm]; exact hiv_lt) hpar]
        refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · -- var_i = iv (8 skips → hi, evm-irrelevant)
          rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_ok_evm (e' := evm)]
          exact hi
        · rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_ok_evm (e' := evm)]
          exact hLn
        · exact lookup_insert_self_fin
        · rw [lookup_insert_ne_fin (by decide)]; exact lookup_insert_self_fin
        · rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_ok_evm (e' := evm)]
          exact hpath
      · -- odd: H(sibling, current)
        have hout_eq : out = accOut evm (foldSib evm path iv) cur := by
          rw [hout, if_neg hpar, hsibfold]
        rw [hout_eq]
        rw [fold_body_odd hidx hpath hi hcur (by rw [← hLn_evm]; exact hiv_lt) hpar]
        refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_ok_evm (e' := evm)]
          exact hi
        · rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_ok_evm (e' := evm)]
          exact hLn
        · exact lookup_insert_self_fin
        · rw [lookup_insert_ne_fin (by decide)]; exact lookup_insert_self_fin
        · rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_ok_evm (e' := evm)]
          exact hpath
    obtain ⟨bs, hexec, hbi, hbe, hbidx, hbcur, hbpath⟩ := hbody
    rw [hexec]
    -- match on `Ok …` selects the recurse arm; reviveJump/overwrite? are identities
    dsimp only
    rw [reviveJump_of_isOk' (show isOk (Ok out.2 bs) from trivial)]
    -- post `var_i := add(var_i, 1)` yields `bs` with `var_i ↦ iv + 1`
    have hpost : exec (fb+1) (.Block for_456069591477598358_post) (Ok out.2 bs)
        = Ok out.2 (bs.insert "var_i" (iv + 1)) := by
      unfold _root_.AtomicFlowManager.Common.for_456069591477598358_post
      simp only [cons, nil, AssignPrimCall', evalArgs, evalTail, cons', head',
                 reverse', multifill', PrimCall', Lit', Var', execPrimCall,
                 evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
                 List.singleton_append, EVMAdd', multifill_cons, multifill_nil]
      rw [hbi]; rfl
    rw [hpost, overwrite?_of_Ok]
    -- new evm reads the same path length (accOut writes only [0,64))
    have hpbound : path.val + 32 ≤ 2 ^ 256 := by
      have : 0 ≤ 32 * Ln.val := Nat.zero_le _
      omega
    have hLn' : Ln = out.2.mload path := by
      rw [hLn_evm, hout]; split <;> exact (accOut_mload_high hpath96 hpbound).symm
    -- apply the induction hypothesis at the post-state
    obtain ⟨σ', hσ'⟩ := ih (fuel := fb+1) (evm := out.2)
      (store := bs.insert "var_i" (iv + 1)) (idx := Fin.shiftRight idx 1)
      (cur := out.1) (iv := iv + 1)
      (by exact lookup_insert_self_fin)
      (by rw [lookup_insert_ne_fin (by decide)]; exact hbe)
      (by rw [lookup_insert_ne_fin (by decide)]; exact hbidx)
      (by rw [lookup_insert_ne_fin (by decide)]; exact hbcur)
      (by rw [lookup_insert_ne_fin (by decide)]; exact hbpath)
      (by rw [val_succ (by omega)]; omega)
      hLn'
      (by omega)
    -- foldRoot unfolds one level to the post-state fold
    have hfold : foldRoot evm path (k+1) iv idx cur
        = foldRoot out.2 path k (iv + 1) (Fin.shiftRight idx 1) out.1 := by
      rw [hout]; rfl
    refine ⟨σ', ?_, ?_⟩
    · rw [overwrite?_of_Ok, hfold]; exact hσ'.1
    · rw [hfold]; exact hσ'.2

end

end generated.AtomicFlowManager.AtomicFlowManager
