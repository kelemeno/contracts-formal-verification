import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_2268004712116198193
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr_5303
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_updateLeaf_5205
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_storage_atoms_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_hash_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_update_fold_user

/-
  U4' — closed form of the self-slot-0 specialized wrapper `fun_updateLeaf_5205`.

  Same logic as the ss-parametric inner `fun_updateLeaf` (see
  `imt_update_fold_user.lean`, U4), with the self slot hardwired to 0:
  leaf count at slot 1, nodes array-of-arrays at slot 2, side (roots) array at
  slot 3, and its own extracted loop `Common.for_2268004712116198193` calling
  the `_ptr` accessor variants with literal slot arguments.

  The pure walk is the same `updateWalk`/`updateStep` of the fold file,
  instantiated at `ss := 0`, `base := 2`; only the per-pass body lemmas are
  re-proved against the 5205 loop body (different identifiers and literal
  arguments).  Success path only.  Axiom-free.
-/

namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism

set_option maxRecDepth 6000
set_option maxHeartbeats 8000000
set_option linter.dupNamespace false

private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok]; exact lookup_insert_of_ne h

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

private lemma setEvm_Ok {e e2 : EVMState} {σ : VarStore} :
    (Ok e σ).setEvm e2 = Ok e2 σ := rfl

private lemma primCall_keccakOut' {s : State} {a b : Literal} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (keccakOut s.evm a b).2, [(keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

private lemma lookup_ok_evm {e e' : EVMState} {σ : VarStore} {k : Identifier} :
    (Ok e σ)[k]!! = (Ok e' σ)[k]!! := rfl

/-- **Closed form of `storage_array_index_access_bytes32_dyn_ptr(array, index)`**
(success path, `index < sload(array)`): identical body to the `__dyn` variant —
returns `(keccak(array) + index, 0)` with the `arrOut` evm step. -/
lemma storage_array_index_ptr_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {arr idx : Literal}
    {sv ov : Identifier}
    (hlt : idx < evm.sload arr) :
    execCall (fuel+1) storage_array_index_access_bytes32_dyn_ptr [sv, ov]
        (Ok evm store, [arr, idx])
      = Ok (arrOut evm arr).2
          (Finmap.insert sv ((arrOut evm arr).1 + idx) (Finmap.insert ov 0 store)) := by
  unfold execCall call storage_array_index_access_bytes32_dyn_ptr
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  set s0 := (Ok evm store)☎️⟦["array", "index"], [arr, idx]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["array"]!! = arr := by rw [hs0]; exact lookup_initcall_1
  have hp2 : s0["index"]!! = idx := by rw [hs0]; exact lookup_initcall_2 (by decide)
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq] at hp1 hp2 ⊢
  have hp2e : ∀ e : EVMState, (Ok e σ0)["index"]!! = idx := fun _ => hp2
  -- statement 1: split_expr_0 := sload(array)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [hp1]
  simp only [evm_Ok, insert_Ok]
  -- statement 2: split_expr_1 := lt(index, split_expr_0)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hp2, lookup_insert_self_fin]
  rw [show fromBool (idx < evm.sload arr) = (1 : UInt256) from by
    rw [decide_eq_true hlt]; rfl]
  simp only [insert_Ok]
  -- statement 3: if iszero(split_expr_1) { panic } — skipped
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- statement 4: mstore(0, array)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMMstore', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hp1]
  simp only [evm_Ok, setEvm_Ok]
  -- statement 5: split_expr_2 := keccak256(0, 32)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append]
  rw [primCall_keccakOut']
  simp only [evm_Ok, setEvm_Ok, multifill_cons, multifill_nil]
  rw [show keccakOut (evm.mstore 0 arr) 0 32 = arrOut evm arr from rfl]
  simp only [insert_Ok]
  -- statement 6: slot := add(split_expr_2, index)
  rw [cons, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMAdd', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hp2e]
  simp only [insert_Ok]
  -- statement 7: offset := 0
  rw [cons, nil, Assign']
  simp only [Lit', insert_Ok]
  -- rets [slot, offset] + call wrapper
  rw [reviveJump_of_isOk (by trivial)]
  try simp only [overwrite?_of_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [setStore_ok]
  simp only [multifill_cons, multifill_nil, insert_Ok]

/-- Closed form of the element-0 `_ptr` accessor `…_5303(array)` (nonempty
array): returns `(keccak(array), 0)`. -/
lemma storage_array_index0_ptr_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {arr : Literal}
    {sv ov : Identifier}
    (hne : evm.sload arr ≠ 0) :
    execCall (fuel+1) storage_array_index_access_bytes32_dyn_ptr_5303 [sv, ov]
        (Ok evm store, [arr])
      = Ok (arrOut evm arr).2
          (Finmap.insert sv (arrOut evm arr).1 (Finmap.insert ov 0 store)) := by
  unfold execCall call storage_array_index_access_bytes32_dyn_ptr_5303
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  set s0 := (Ok evm store)☎️⟦["array"], [arr]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["array"]!! = arr := by rw [hs0]; exact lookup_initcall_1
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq] at hp1 ⊢
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [hp1]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool (evm.sload arr = 0) = (0 : UInt256) from by
    rw [decide_eq_false hne]; rfl]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMMstore', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hp1]
  simp only [evm_Ok, setEvm_Ok]
  rw [cons, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append]
  rw [primCall_keccakOut']
  simp only [evm_Ok, setEvm_Ok, multifill_cons, multifill_nil]
  rw [show keccakOut (evm.mstore 0 arr) 0 32 = arrOut evm arr from rfl]
  simp only [insert_Ok]
  rw [cons, nil, Assign']
  simp only [Lit', insert_Ok]
  rw [reviveJump_of_isOk (by trivial)]
  try simp only [overwrite?_of_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [lookup_insert_self_fin]
  rw [setStore_ok]
  simp only [multifill_cons, multifill_nil, insert_Ok]

/-! ## The 5205 loop sub-blocks (literal slots 2 / 3, `_ptr` accessors) -/

/-- Odd-branch sibling read of the 5205 loop: element `index − 1` of the
level-`lvl` node array (array-of-arrays at slot 2) into `split_expr_8`. -/
private lemma oddRead5205_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {lvl idx : Literal}
    (hlvl : (Ok evm σ)["var_i"]!! = lvl)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hidx0 : idx ≠ 0)
    (hb1 : lvl < evm.sload 2)
    (hb2 : idx - 1 < (arrOut evm 2).2.sload ((arrOut evm 2).1 + lvl)) :
    exec (fuel+1) (.Block
        [LetCall ["_5", "_6"] storage_array_index_access_bytes32_dyn_ptr
           [Lit 2, Var "var_i"],
         LetCall ["split_expr_6"] checked_sub_uint256 [Var "var_index"],
         LetCall ["_7", "_8"] storage_array_index_access_bytes32_dyn_ptr
           [Var "_5", Var "split_expr_6"],
         LetPrimCall ["split_expr_7"] .Sload [Var "_7"],
         LetCall ["split_expr_8"] extract_from_storage_value_dynamict_bytes32
           [Var "split_expr_7", Var "_8"]]) (Ok evm σ)
      = Ok (sibRead evm 2 lvl (idx - 1)).2
          (Finmap.insert "split_expr_8" (sibRead evm 2 lvl (idx - 1)).1
            (Finmap.insert "split_expr_7" (sibRead evm 2 lvl (idx - 1)).1
              (Finmap.insert "_7"
                ((arrOut (arrOut evm 2).2 ((arrOut evm 2).1 + lvl)).1 + (idx - 1))
                (Finmap.insert "_8" 0
                  (Finmap.insert "split_expr_6" (idx - 1)
                    (Finmap.insert "_5" ((arrOut evm 2).1 + lvl)
                      (Finmap.insert "_6" 0 σ))))))) := by
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  -- statement 1: _5, _6 := arrayaccess(2, var_i)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [hlvl]
  rw [storage_array_index_ptr_call hb1]
  -- statement 2: split_expr_6 := checked_sub(var_index)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hidxe]
  rw [checked_sub_call hidx0]
  -- statement 3: _7, _8 := arrayaccess(_5, split_expr_6)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [lookup_insert_self_fin]
  rw [storage_array_index_ptr_call hb2]
  -- statement 4: split_expr_7 := sload(_7)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [evm_Ok, insert_Ok]
  -- statement 5: split_expr_8 := extract(split_expr_7, _8)
  rw [cons, nil, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [extract_call_0]
  rfl

/-- Even-branch (non-edge) sibling read of the 5205 loop: element `index + 1`
of the level-`lvl` node array into `expr`. -/
private lemma evenRead5205_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {lvl idx : Literal}
    (hlvl : (Ok evm σ)["var_i"]!! = lvl)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hadd : idx.val + 1 < 2 ^ 256)
    (hb1 : lvl < evm.sload 2)
    (hb2 : idx + 1 < (arrOut evm 2).2.sload ((arrOut evm 2).1 + lvl)) :
    exec (fuel+1) (.Block
        [LetCall ["_9", "_10"] storage_array_index_access_bytes32_dyn_ptr
           [Lit 2, Var "var_i"],
         LetCall ["split_expr_9"] checked_add_uint256 [Var "var_index"],
         LetCall ["_11", "_12"] storage_array_index_access_bytes32_dyn_ptr
           [Var "_9", Var "split_expr_9"],
         LetPrimCall ["split_expr_10"] .Sload [Var "_11"],
         AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
           [Var "split_expr_10", Var "_12"]]) (Ok evm σ)
      = Ok (sibRead evm 2 lvl (idx + 1)).2
          (Finmap.insert "expr" (sibRead evm 2 lvl (idx + 1)).1
            (Finmap.insert "split_expr_10" (sibRead evm 2 lvl (idx + 1)).1
              (Finmap.insert "_11"
                ((arrOut (arrOut evm 2).2 ((arrOut evm 2).1 + lvl)).1 + (idx + 1))
                (Finmap.insert "_12" 0
                  (Finmap.insert "split_expr_9" (idx + 1)
                    (Finmap.insert "_9" ((arrOut evm 2).1 + lvl)
                      (Finmap.insert "_10" 0 σ))))))) := by
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [hlvl]
  rw [storage_array_index_ptr_call hb1]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hidxe]
  rw [checked_add_call hadd]
  rw [show ((Ok (arrOut evm 2).2
      (Finmap.insert "_9" ((arrOut evm 2).1 + lvl) (Finmap.insert "_10" 0 σ)) : State)⟦"split_expr_9" ↦ idx + 1⟧)
      = Ok (arrOut evm 2).2 (Finmap.insert "split_expr_9" (idx + 1)
          (Finmap.insert "_9" ((arrOut evm 2).1 + lvl) (Finmap.insert "_10" 0 σ))) from rfl]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [lookup_insert_self_fin]
  rw [storage_array_index_ptr_call hb2]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [evm_Ok, insert_Ok]
  rw [cons, nil, AssignCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [extract_call_0]
  rfl

/-- Edge-branch read of the 5205 loop: element `lvl` of the side (roots) array
at slot 3 into `expr`. -/
private lemma edgeRead5205_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {lvl : Literal}
    (hlvl : (Ok evm σ)["var_i"]!! = lvl)
    (hb : lvl < evm.sload 3) :
    exec (fuel+1) (.Block
        [LetCall ["_13", "_14"] storage_array_index_access_bytes32_dyn_ptr
           [Lit 3, Var "var_i"],
         LetPrimCall ["split_expr_11"] .Sload [Var "_13"],
         AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
           [Var "split_expr_11", Var "_14"]]) (Ok evm σ)
      = Ok (sideRead evm 3 lvl).2
          (Finmap.insert "expr" (sideRead evm 3 lvl).1
            (Finmap.insert "split_expr_11" (sideRead evm 3 lvl).1
              (Finmap.insert "_13" ((arrOut evm 3).1 + lvl)
                (Finmap.insert "_14" 0 σ)))) := by
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [hlvl]
  rw [storage_array_index_ptr_call hb]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [evm_Ok, insert_Ok]
  rw [cons, nil, AssignCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [extract_call_0]
  rfl

/-- Div/store prep block of the 5205 loop: halves `var_index` and
`var_maxNodeNumber`, computes the parent write slot — element `index >> 1` of
the level-`lvl+1` array at slot 2. -/
private lemma divStore5205_prep_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {lvl idx maxN : Literal}
    (hlvl : (Ok evm σ)["var_i"]!! = lvl)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hmax : (Ok evm σ)["var_maxNodeNumber"]!! = maxN)
    (haddl : lvl.val + 1 < 2 ^ 256)
    (hb1 : lvl + 1 < evm.sload 2)
    (hb2 : Fin.shiftRight idx 1
        < (arrOut evm 2).2.sload ((arrOut evm 2).1 + (lvl + 1))) :
    exec (fuel+1) (.Block
        [AssignCall ["var_index"] checked_div_uint256 [Var "var_index"],
         AssignCall ["var_maxNodeNumber"] checked_div_uint256 [Var "var_maxNodeNumber"],
         LetCall ["split_expr_12"] checked_add_uint256 [Var "var_i"],
         LetCall ["_15", "_16"] storage_array_index_access_bytes32_dyn_ptr
           [Lit 2, Var "split_expr_12"],
         LetCall ["_17", "_18"] storage_array_index_access_bytes32_dyn_ptr
           [Var "_15", Var "var_index"]]) (Ok evm σ)
      = Ok (arrOut (arrOut evm 2).2 ((arrOut evm 2).1 + (lvl + 1))).2
          (Finmap.insert "_17"
              ((arrOut (arrOut evm 2).2 ((arrOut evm 2).1 + (lvl + 1))).1
                + Fin.shiftRight idx 1)
            (Finmap.insert "_18" 0
              (Finmap.insert "_15" ((arrOut evm 2).1 + (lvl + 1))
                (Finmap.insert "_16" 0
                  (Finmap.insert "split_expr_12" (lvl + 1)
                    (Finmap.insert "var_maxNodeNumber" (Fin.shiftRight maxN 1)
                      (Finmap.insert "var_index" (Fin.shiftRight idx 1) σ))))))) := by
  have hmaxe : ∀ e : EVMState, (Ok e σ)["var_maxNodeNumber"]!! = maxN := fun _ => hmax
  have hlvle : ∀ e : EVMState, (Ok e σ)["var_i"]!! = lvl := fun _ => hlvl
  rw [cons, AssignCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [hidx, div2_call]
  simp only [insert_Ok]
  rw [cons, AssignCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), hmaxe, div2_call]
  simp only [insert_Ok]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hlvle]
  rw [checked_add_call haddl]
  simp only [insert_Ok]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [storage_array_index_ptr_call hb1]
  rw [cons, nil, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [storage_array_index_ptr_call hb2]

/-- Store step of the 5205 loop: plain `sstore` of the recomputed node. -/
private lemma store5205_call_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {wslot cur : Literal}
    (h17 : (Ok evm σ)["_17"]!! = wslot)
    (h18 : (Ok evm σ)["_18"]!! = 0)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur) :
    exec (fuel+1) (.Block
        [ExprStmtCall update_storage_value_bytes32_to_bytes32
           [Var "_17", Var "_18", Var "var_currentHash"]]) (Ok evm σ)
      = Ok (evm.sstore wslot cur) σ := by
  rw [cons, nil, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [h17, h18, hcur]
  rw [update_storage_call_0]

/-! ## The 5205 loop-body passes (odd / even / edge / break) -/

/-- The odd switch arm of the 5205 loop: sibling read then hash. -/
private lemma arm_odd_5205
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {i idx cur : Literal}
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur)
    (hidx0 : idx ≠ 0)
    (hb1 : i < evm.sload 2)
    (hb2 : idx - 1 < (arrOut evm 2).2.sload ((arrOut evm 2).1 + i)) :
    exec (fuel+1) (.Block
        [.Block
          [LetCall ["_5", "_6"] storage_array_index_access_bytes32_dyn_ptr
             [Lit 2, Var "var_i"],
           LetCall ["split_expr_6"] checked_sub_uint256 [Var "var_index"],
           LetCall ["_7", "_8"] storage_array_index_access_bytes32_dyn_ptr
             [Var "_5", Var "split_expr_6"],
           LetPrimCall ["split_expr_7"] .Sload [Var "_7"],
           LetCall ["split_expr_8"] extract_from_storage_value_dynamict_bytes32
             [Var "split_expr_7", Var "_8"]],
         .Block
          [AssignCall ["var_currentHash"] fun_efficientHash
             [Var "split_expr_8", Var "var_currentHash"]]]) (Ok evm σ)
      = Ok (accOut (sibRead evm 2 i (idx - 1)).2 (sibRead evm 2 i (idx - 1)).1 cur).2
          (Finmap.insert "var_currentHash"
              (accOut (sibRead evm 2 i (idx - 1)).2 (sibRead evm 2 i (idx - 1)).1 cur).1
            (Finmap.insert "split_expr_8" (sibRead evm 2 i (idx - 1)).1
              (Finmap.insert "split_expr_7" (sibRead evm 2 i (idx - 1)).1
                (Finmap.insert "_7"
                    ((arrOut (arrOut evm 2).2 ((arrOut evm 2).1 + i)).1 + (idx - 1))
                  (Finmap.insert "_8" 0
                    (Finmap.insert "split_expr_6" (idx - 1)
                      (Finmap.insert "_5" ((arrOut evm 2).1 + i)
                        (Finmap.insert "_6" 0 σ)))))))) := by
  have hcure : ∀ e : EVMState, (Ok e σ)["var_currentHash"]!! = cur := fun _ => hcur
  rw [cons]
  rw [oddRead5205_block hi hidx hidx0 hb1 hb2]
  rw [cons, nil, cons, nil, AssignCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide)]
  rw [hcure]
  rw [efficientHash_call_acc]
  try simp only [insert_Ok]

/-- The even (non-edge) default arm of the 5205 loop: inner max-check switch
selects the sibling read at `idx + 1`, then hash `H(cur ‖ sib)`. -/
private lemma arm_even_5205
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {i idx maxN cur : Literal}
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hmax : (Ok evm σ)["var_maxNodeNumber"]!! = maxN)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur)
    (hne : maxN ≠ idx)
    (hadd : idx.val + 1 < 2 ^ 256)
    (hb1 : i < evm.sload 2)
    (hb2 : idx + 1 < (arrOut evm 2).2.sload ((arrOut evm 2).1 + i)) :
    exec (fuel+1) (.Block
        [LetEq "expr" (Lit 0),
         Switch (PrimCall .Eq [Var "var_maxNodeNumber", Var "var_index"])
           [(0, [LetCall ["_9", "_10"] storage_array_index_access_bytes32_dyn_ptr
                   [Lit 2, Var "var_i"],
                 LetCall ["split_expr_9"] checked_add_uint256 [Var "var_index"],
                 LetCall ["_11", "_12"] storage_array_index_access_bytes32_dyn_ptr
                   [Var "_9", Var "split_expr_9"],
                 LetPrimCall ["split_expr_10"] .Sload [Var "_11"],
                 AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
                   [Var "split_expr_10", Var "_12"]])]
           [LetCall ["_13", "_14"] storage_array_index_access_bytes32_dyn_ptr
              [Lit 3, Var "var_i"],
            LetPrimCall ["split_expr_11"] .Sload [Var "_13"],
            AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
              [Var "split_expr_11", Var "_14"]],
         AssignCall ["var_currentHash"] fun_efficientHash
           [Var "var_currentHash", Var "expr"]]) (Ok evm σ)
      = Ok (accOut (sibRead evm 2 i (idx + 1)).2 cur (sibRead evm 2 i (idx + 1)).1).2
          (Finmap.insert "var_currentHash"
              (accOut (sibRead evm 2 i (idx + 1)).2 cur (sibRead evm 2 i (idx + 1)).1).1
            (Finmap.insert "expr" (sibRead evm 2 i (idx + 1)).1
              (Finmap.insert "split_expr_10" (sibRead evm 2 i (idx + 1)).1
                (Finmap.insert "_11"
                    ((arrOut (arrOut evm 2).2 ((arrOut evm 2).1 + i)).1 + (idx + 1))
                  (Finmap.insert "_12" 0
                    (Finmap.insert "split_expr_9" (idx + 1)
                      (Finmap.insert "_9" ((arrOut evm 2).1 + i)
                        (Finmap.insert "_10" 0
                          (Finmap.insert "expr" 0 σ))))))))) := by
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  have hmaxe : ∀ e : EVMState, (Ok e σ)["var_maxNodeNumber"]!! = maxN := fun _ => hmax
  have hcure : ∀ e : EVMState, (Ok e σ)["var_currentHash"]!! = cur := fun _ => hcur
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  -- the inner max-check switch: eq(maxN, idx) = 0 → case-0 arm (even read)
  rw [cons, Switch']
  simp only [evalArgs, evalTail, cons', head', reverse', PrimCall', Lit', Var',
             execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil,
             List.nil_append, List.singleton_append, EVMEq',
             execSwitchCases, List.foldr]
  rw [lookup_insert_ne_fin (by decide), hmaxe]
  rw [lookup_insert_ne_fin (by decide), hidxe]
  rw [show fromBool (maxN = idx) = (0 : UInt256) from by
    rw [decide_eq_false hne]; rfl]
  simp only [List.head!]
  -- the selected even-read arm
  rw [evenRead5205_block (lvl := i) (idx := idx)
    (by rw [lookup_insert_ne_fin (by decide)]; exact hie _)
    (by rw [lookup_insert_ne_fin (by decide)]; exact hidxe _)
    hadd hb1 hb2]
  try simp only [if_true]
  -- the hash: var_currentHash := fun_efficientHash(var_currentHash, expr)
  rw [cons, nil, AssignCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
  rw [hcure]
  rw [lookup_insert_self_fin]
  rw [efficientHash_call_acc]
  try simp only [insert_Ok]

/-- The edge default arm of the 5205 loop (`maxNodeNumber = index`): the inner
max-check selects the side-array read at slot 3. -/
private lemma arm_edge_5205
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {i idx maxN cur : Literal}
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hmax : (Ok evm σ)["var_maxNodeNumber"]!! = maxN)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur)
    (heq : maxN = idx)
    (hbe : i < evm.sload 3) :
    exec (fuel+1) (.Block
        [LetEq "expr" (Lit 0),
         Switch (PrimCall .Eq [Var "var_maxNodeNumber", Var "var_index"])
           [(0, [LetCall ["_9", "_10"] storage_array_index_access_bytes32_dyn_ptr
                   [Lit 2, Var "var_i"],
                 LetCall ["split_expr_9"] checked_add_uint256 [Var "var_index"],
                 LetCall ["_11", "_12"] storage_array_index_access_bytes32_dyn_ptr
                   [Var "_9", Var "split_expr_9"],
                 LetPrimCall ["split_expr_10"] .Sload [Var "_11"],
                 AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
                   [Var "split_expr_10", Var "_12"]])]
           [LetCall ["_13", "_14"] storage_array_index_access_bytes32_dyn_ptr
              [Lit 3, Var "var_i"],
            LetPrimCall ["split_expr_11"] .Sload [Var "_13"],
            AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
              [Var "split_expr_11", Var "_14"]],
         AssignCall ["var_currentHash"] fun_efficientHash
           [Var "var_currentHash", Var "expr"]]) (Ok evm σ)
      = Ok (accOut (sideRead evm 3 i).2 cur (sideRead evm 3 i).1).2
          (Finmap.insert "var_currentHash"
              (accOut (sideRead evm 3 i).2 cur (sideRead evm 3 i).1).1
            (Finmap.insert "expr" (sideRead evm 3 i).1
              (Finmap.insert "split_expr_11" (sideRead evm 3 i).1
                (Finmap.insert "_13" ((arrOut evm 3).1 + i)
                  (Finmap.insert "_14" 0
                    (Finmap.insert "expr" 0 σ)))))) := by
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  have hmaxe : ∀ e : EVMState, (Ok e σ)["var_maxNodeNumber"]!! = maxN := fun _ => hmax
  have hcure : ∀ e : EVMState, (Ok e σ)["var_currentHash"]!! = cur := fun _ => hcur
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  -- the inner max-check switch: eq(maxN, idx) = 1 → DEFAULT arm (edge read)
  rw [cons, Switch']
  simp only [evalArgs, evalTail, cons', head', reverse', PrimCall', Lit', Var',
             execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil,
             List.nil_append, List.singleton_append, EVMEq',
             execSwitchCases, List.foldr]
  rw [lookup_insert_ne_fin (by decide), hmaxe]
  rw [lookup_insert_ne_fin (by decide), hidxe]
  rw [show fromBool (maxN = idx) = (1 : UInt256) from by
    rw [decide_eq_true heq]; rfl]
  simp only [List.head!]
  rw [if_neg (by decide : ¬ ((0 : Literal) = 1))]
  -- the selected edge-read arm
  rw [edgeRead5205_block (lvl := i)
    (by rw [lookup_insert_ne_fin (by decide)]; exact hie _)
    hbe]
  try simp only [if_true]
  -- the hash: var_currentHash := fun_efficientHash(var_currentHash, expr)
  rw [cons, nil, AssignCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide)]
  rw [hcure]
  rw [lookup_insert_self_fin]
  rw [efficientHash_call_acc]
  try simp only [insert_Ok]

/-- **One odd-index body pass** of the 5205 loop equals `stepOdd _ 2`. -/
lemma updateBody_odd_5205
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    {i idx maxN cur : Literal}
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hmax : (Ok evm σ)["var_maxNodeNumber"]!! = maxN)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur)
    (hbreak : i < evm.sload 0)
    (hodd : Fin.land idx 1 ≠ 0)
    (hb1 : i < evm.sload 2)
    (hb2 : idx - 1 < (arrOut evm 2).2.sload ((arrOut evm 2).1 + i))
    (haddl : i.val + 1 < 2 ^ 256)
    (hb3 : i + 1
      < (accOut (sibRead evm 2 i (idx - 1)).2 (sibRead evm 2 i (idx - 1)).1 cur).2.sload 2)
    (hb4 : Fin.shiftRight idx 1
      < (arrOut (accOut (sibRead evm 2 i (idx - 1)).2 (sibRead evm 2 i (idx - 1)).1 cur).2
            2).2.sload
          ((arrOut (accOut (sibRead evm 2 i (idx - 1)).2 (sibRead evm 2 i (idx - 1)).1 cur).2
              2).1 + (i + 1))) :
    exec (fuel+1) (.Block L2InteropCommitmentTree.Common.for_2268004712116198193_body)
        (Ok evm σ)
      = Ok (stepOdd evm 2 i idx cur).2
          (Finmap.insert "_17"
              ((arrOut (arrOut (accOut (sibRead evm 2 i (idx - 1)).2
                    (sibRead evm 2 i (idx - 1)).1 cur).2 2).2
                  ((arrOut (accOut (sibRead evm 2 i (idx - 1)).2
                    (sibRead evm 2 i (idx - 1)).1 cur).2 2).1 + (i + 1))).1
                + Fin.shiftRight idx 1)
            (Finmap.insert "_18" 0
              (Finmap.insert "_15"
                  ((arrOut (accOut (sibRead evm 2 i (idx - 1)).2
                    (sibRead evm 2 i (idx - 1)).1 cur).2 2).1 + (i + 1))
                (Finmap.insert "_16" 0
                  (Finmap.insert "split_expr_12" (i + 1)
                    (Finmap.insert "var_maxNodeNumber" (Fin.shiftRight maxN 1)
                      (Finmap.insert "var_index" (Fin.shiftRight idx 1)
                        (Finmap.insert "var_currentHash" (stepOdd evm 2 i idx cur).1
                          (Finmap.insert "split_expr_8" (sibRead evm 2 i (idx - 1)).1
                            (Finmap.insert "split_expr_7" (sibRead evm 2 i (idx - 1)).1
                              (Finmap.insert "_7"
                                  ((arrOut (arrOut evm 2).2 ((arrOut evm 2).1 + i)).1
                                    + (idx - 1))
                                (Finmap.insert "_8" 0
                                  (Finmap.insert "split_expr_6" (idx - 1)
                                    (Finmap.insert "_5" ((arrOut evm 2).1 + i)
                                      (Finmap.insert "_6" 0
                                        (Finmap.insert "split_expr_5" (Fin.land idx 1)
                                          (Finmap.insert "split_expr_4" 1
                                            (Finmap.insert "split_expr_3" (evm.sload 0)
                                              σ)))))))))))))))))) := by
  have hidx0 : idx ≠ 0 := by
    intro h
    exact hodd (by rw [h]; decide)
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  have hmaxe : ∀ e : EVMState, (Ok e σ)["var_maxNodeNumber"]!! = maxN := fun _ => hmax
  have hcure : ∀ e : EVMState, (Ok e σ)["var_currentHash"]!! = cur := fun _ => hcur
  unfold _root_.L2InteropCommitmentTree.Common.for_2268004712116198193_body
  -- statement 1: split_expr_3 := sload(0)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  -- statement 2: split_expr_4 := lt(var_i, split_expr_3)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hie, lookup_insert_self_fin]
  rw [show fromBool (i < evm.sload 0) = (1 : UInt256) from by
    rw [decide_eq_true hbreak]; rfl]
  simp only [insert_Ok]
  -- statement 3: if iszero(split_expr_4) {break} — skipped
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- statement 4: split_expr_5 := mod_uint256(var_index)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hidxe]
  rw [mod2_call]
  simp only [insert_Ok]
  -- statement 5: the parity switch — scrutinee iszero(split_expr_5) = 0 (odd)
  rw [cons, Switch']
  simp only [evalArgs, evalTail, cons', head', reverse', PrimCall', Lit', Var',
             execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil,
             List.nil_append, List.singleton_append, EVMIszero',
             execSwitchCases, List.foldr]
  rw [lookup_insert_self_fin]
  rw [show fromBool (Fin.land idx 1 = 0) = (0 : UInt256) from by
    rw [decide_eq_false hodd]; rfl]
  simp only [List.head!]
  -- the selected case-0 arm: [oddRead block, hash block]
  rw [arm_odd_5205 (i := i) (idx := idx) (cur := cur)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hie _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hidxe _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hcure _)
    hidx0 hb1 hb2]
  try simp only [if_true]
  -- the div/store prep block
  rw [cons]
  rw [divStore5205_prep_block (lvl := i) (idx := idx) (maxN := maxN)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hie _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hidxe _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hmaxe _)
    haddl hb3 hb4]
  -- the store block
  rw [cons, nil]
  rw [store5205_call_block
    (by rw [lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_self_fin])]
  rfl

/-- **One even-index (non-edge) body pass** of the 5205 loop equals
`stepEven _ 2`. -/
lemma updateBody_even_5205
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    {i idx maxN cur : Literal}
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hmax : (Ok evm σ)["var_maxNodeNumber"]!! = maxN)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur)
    (hbreak : i < evm.sload 0)
    (heven : Fin.land idx 1 = 0)
    (hne : maxN ≠ idx)
    (hadd : idx.val + 1 < 2 ^ 256)
    (hb1 : i < evm.sload 2)
    (hb2 : idx + 1 < (arrOut evm 2).2.sload ((arrOut evm 2).1 + i))
    (haddl : i.val + 1 < 2 ^ 256)
    (hb3 : i + 1
      < (accOut (sibRead evm 2 i (idx + 1)).2 cur (sibRead evm 2 i (idx + 1)).1).2.sload 2)
    (hb4 : Fin.shiftRight idx 1
      < (arrOut (accOut (sibRead evm 2 i (idx + 1)).2 cur (sibRead evm 2 i (idx + 1)).1).2
            2).2.sload
          ((arrOut (accOut (sibRead evm 2 i (idx + 1)).2 cur (sibRead evm 2 i (idx + 1)).1).2
              2).1 + (i + 1))) :
    exec (fuel+1) (.Block L2InteropCommitmentTree.Common.for_2268004712116198193_body)
        (Ok evm σ)
      = Ok (stepEven evm 2 i idx cur).2
          (Finmap.insert "_17"
              ((arrOut (arrOut (accOut (sibRead evm 2 i (idx + 1)).2 cur
                    (sibRead evm 2 i (idx + 1)).1).2 2).2
                  ((arrOut (accOut (sibRead evm 2 i (idx + 1)).2 cur
                    (sibRead evm 2 i (idx + 1)).1).2 2).1 + (i + 1))).1
                + Fin.shiftRight idx 1)
            (Finmap.insert "_18" 0
              (Finmap.insert "_15"
                  ((arrOut (accOut (sibRead evm 2 i (idx + 1)).2 cur
                    (sibRead evm 2 i (idx + 1)).1).2 2).1 + (i + 1))
                (Finmap.insert "_16" 0
                  (Finmap.insert "split_expr_12" (i + 1)
                    (Finmap.insert "var_maxNodeNumber" (Fin.shiftRight maxN 1)
                      (Finmap.insert "var_index" (Fin.shiftRight idx 1)
                        (Finmap.insert "var_currentHash" (stepEven evm 2 i idx cur).1
                          (Finmap.insert "expr" (sibRead evm 2 i (idx + 1)).1
                            (Finmap.insert "split_expr_10" (sibRead evm 2 i (idx + 1)).1
                              (Finmap.insert "_11"
                                  ((arrOut (arrOut evm 2).2 ((arrOut evm 2).1 + i)).1
                                    + (idx + 1))
                                (Finmap.insert "_12" 0
                                  (Finmap.insert "split_expr_9" (idx + 1)
                                    (Finmap.insert "_9" ((arrOut evm 2).1 + i)
                                      (Finmap.insert "_10" 0
                                        (Finmap.insert "expr" 0
                                          (Finmap.insert "split_expr_5" (Fin.land idx 1)
                                            (Finmap.insert "split_expr_4" 1
                                              (Finmap.insert "split_expr_3" (evm.sload 0)
                                                σ))))))))))))))))))) := by
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  have hmaxe : ∀ e : EVMState, (Ok e σ)["var_maxNodeNumber"]!! = maxN := fun _ => hmax
  have hcure : ∀ e : EVMState, (Ok e σ)["var_currentHash"]!! = cur := fun _ => hcur
  unfold _root_.L2InteropCommitmentTree.Common.for_2268004712116198193_body
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hie, lookup_insert_self_fin]
  rw [show fromBool (i < evm.sload 0) = (1 : UInt256) from by
    rw [decide_eq_true hbreak]; rfl]
  simp only [insert_Ok]
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hidxe]
  rw [mod2_call]
  simp only [insert_Ok]
  -- the parity switch: scrutinee iszero(land idx 1) = 1 → DEFAULT arm
  rw [cons, Switch']
  simp only [evalArgs, evalTail, cons', head', reverse', PrimCall', Lit', Var',
             execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil,
             List.nil_append, List.singleton_append, EVMIszero',
             execSwitchCases, List.foldr]
  rw [lookup_insert_self_fin]
  rw [show fromBool (Fin.land idx 1 = 0) = (1 : UInt256) from by
    rw [decide_eq_true heven]; rfl]
  simp only [List.head!]
  rw [if_neg (by decide : ¬ ((0 : Literal) = 1))]
  -- the default arm = the even/edge selector
  rw [arm_even_5205 (i := i) (idx := idx) (maxN := maxN) (cur := cur)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hie _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hidxe _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hmaxe _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hcure _)
    hne hadd hb1 hb2]
  try simp only [if_true]
  -- the div/store prep block
  rw [cons]
  rw [divStore5205_prep_block (lvl := i) (idx := idx) (maxN := maxN)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact hie _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact hidxe _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact hmaxe _)
    haddl hb3 hb4]
  -- the store block
  rw [cons, nil]
  rw [store5205_call_block
    (by rw [lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_self_fin])]
  rfl

/-- **One edge body pass** (`maxNodeNumber = index`) of the 5205 loop equals
`stepEdge _ 0 2`. -/
lemma updateBody_edge_5205
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    {i idx maxN cur : Literal}
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hmax : (Ok evm σ)["var_maxNodeNumber"]!! = maxN)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur)
    (hbreak : i < evm.sload 0)
    (heven : Fin.land idx 1 = 0)
    (heq : maxN = idx)
    (hbe : i < evm.sload 3)
    (haddl : i.val + 1 < 2 ^ 256)
    (hb3 : i + 1
      < (accOut (sideRead evm 3 i).2 cur (sideRead evm 3 i).1).2.sload 2)
    (hb4 : Fin.shiftRight idx 1
      < (arrOut (accOut (sideRead evm 3 i).2 cur (sideRead evm 3 i).1).2 2).2.sload
          ((arrOut (accOut (sideRead evm 3 i).2 cur (sideRead evm 3 i).1).2 2).1 + (i + 1))) :
    exec (fuel+1) (.Block L2InteropCommitmentTree.Common.for_2268004712116198193_body)
        (Ok evm σ)
      = Ok (stepEdge evm 0 2 i idx cur).2
          (Finmap.insert "_17"
              ((arrOut (arrOut (accOut (sideRead evm 3 i).2 cur
                    (sideRead evm 3 i).1).2 2).2
                  ((arrOut (accOut (sideRead evm 3 i).2 cur
                    (sideRead evm 3 i).1).2 2).1 + (i + 1))).1
                + Fin.shiftRight idx 1)
            (Finmap.insert "_18" 0
              (Finmap.insert "_15"
                  ((arrOut (accOut (sideRead evm 3 i).2 cur
                    (sideRead evm 3 i).1).2 2).1 + (i + 1))
                (Finmap.insert "_16" 0
                  (Finmap.insert "split_expr_12" (i + 1)
                    (Finmap.insert "var_maxNodeNumber" (Fin.shiftRight maxN 1)
                      (Finmap.insert "var_index" (Fin.shiftRight idx 1)
                        (Finmap.insert "var_currentHash" (stepEdge evm 0 2 i idx cur).1
                          (Finmap.insert "expr" (sideRead evm 3 i).1
                            (Finmap.insert "split_expr_11" (sideRead evm 3 i).1
                              (Finmap.insert "_13" ((arrOut evm 3).1 + i)
                                (Finmap.insert "_14" 0
                                  (Finmap.insert "expr" 0
                                    (Finmap.insert "split_expr_5" (Fin.land idx 1)
                                      (Finmap.insert "split_expr_4" 1
                                        (Finmap.insert "split_expr_3" (evm.sload 0)
                                          σ)))))))))))))))) := by
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  have hmaxe : ∀ e : EVMState, (Ok e σ)["var_maxNodeNumber"]!! = maxN := fun _ => hmax
  have hcure : ∀ e : EVMState, (Ok e σ)["var_currentHash"]!! = cur := fun _ => hcur
  unfold _root_.L2InteropCommitmentTree.Common.for_2268004712116198193_body
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hie, lookup_insert_self_fin]
  rw [show fromBool (i < evm.sload 0) = (1 : UInt256) from by
    rw [decide_eq_true hbreak]; rfl]
  simp only [insert_Ok]
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hidxe]
  rw [mod2_call]
  simp only [insert_Ok]
  rw [cons, Switch']
  simp only [evalArgs, evalTail, cons', head', reverse', PrimCall', Lit', Var',
             execPrimCall, evalPrimCall, List.reverse_cons, List.reverse_nil,
             List.nil_append, List.singleton_append, EVMIszero',
             execSwitchCases, List.foldr]
  rw [lookup_insert_self_fin]
  rw [show fromBool (Fin.land idx 1 = 0) = (1 : UInt256) from by
    rw [decide_eq_true heven]; rfl]
  simp only [List.head!]
  rw [if_neg (by decide : ¬ ((0 : Literal) = 1))]
  rw [arm_edge_5205 (i := i) (idx := idx) (maxN := maxN) (cur := cur)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hie _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hidxe _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hmaxe _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hcure _)
    heq hbe]
  try simp only [if_true]
  rw [cons]
  rw [divStore5205_prep_block (lvl := i) (idx := idx) (maxN := maxN)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hie _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hidxe _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hmaxe _)
    haddl hb3 hb4]
  rw [cons, nil]
  rw [store5205_call_block
    (by rw [lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_self_fin])]
  rfl

/-- Statements are the identity on checkpoint states. -/
private lemma exec_checkpoint {c : Jump} {fuel : ℕ} {stmt : Stmt} :
    exec fuel stmt (Checkpoint c) = Checkpoint c := by
  have h := Clear.JumpLemmas.exec_Jump (c := c) (s := Checkpoint c) (fuel := fuel) (stmt := stmt) rfl
  rcases hres : exec fuel stmt (Checkpoint c) with _ | _ | c'
  · rw [hres] at h; exact absurd h (by unfold isJump; simp)
  · rw [hres] at h; exact absurd h (by unfold isJump; simp)
  · rw [hres] at h
    have : c = c' := h
    rw [this]

/-- A lone `break` block checkpoints the state. -/
private lemma break_block {fuel : ℕ} {evm : EVMState} {σ : VarStore} :
    exec (fuel+1) (.Block [Stmt.Break]) (Ok evm σ) = Checkpoint (.Break evm σ) := by
  rw [cons, nil, Break']
  rfl

/-- **The break pass** of the 5205 loop: when the level counter has reached the
level count at slot 0, the body breaks out immediately. -/
lemma updateBody_break_5205
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {i : Literal}
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hstop : ¬ (i < evm.sload 0)) :
    exec (fuel+1) (.Block L2InteropCommitmentTree.Common.for_2268004712116198193_body)
        (Ok evm σ)
      = Checkpoint (.Break evm
          (Finmap.insert "split_expr_4" 0
            (Finmap.insert "split_expr_3" (evm.sload 0) σ))) := by
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  unfold _root_.L2InteropCommitmentTree.Common.for_2268004712116198193_body
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hie, lookup_insert_self_fin]
  rw [show fromBool (i < evm.sload 0) = (0 : UInt256) from by
    rw [decide_eq_false hstop]; rfl]
  simp only [insert_Ok]
  -- the break-if fires
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [head', List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  rw [break_block]
  -- the remaining statements pass the checkpoint through
  rw [cons, exec_checkpoint, cons, exec_checkpoint, cons, exec_checkpoint,
      cons, nil, exec_checkpoint]

/-! ## The 5205 loop as the pure walk (`ss := 0`, `base := 2`) -/

/-- **The 5205 `updateLeaf` loop is the pure walk.**  Under the per-level
bounds (`hpass`, the same `WalkOK` of the fold file at `ss := 0`, `base := 2`)
and level-count slot-0 stability (`hssinv`), the loop equals `updateWalk`. -/
lemma update_loop_5205 :
    ∀ (k : ℕ) {fuel : ℕ} {evm : EVMState} {σ : VarStore}
      {i idx maxN cur : Literal},
    (Ok evm σ)["var_i"]!! = i →
    (Ok evm σ)["var_index"]!! = idx →
    (Ok evm σ)["var_maxNodeNumber"]!! = maxN →
    (Ok evm σ)["var_currentHash"]!! = cur →
    i.val + k = (evm.sload 0).val →
    (∀ j, j < k → WalkOK 0 2 (updateWalk 0 2 j evm i idx maxN cur)) →
    (∀ j, j ≤ k → ((updateWalk 0 2 j evm i idx maxN cur).1).sload 0 = evm.sload 0) →
    2 * k + 3 ≤ fuel →
    ∃ σ' : VarStore,
      exec fuel (.For L2InteropCommitmentTree.Common.for_2268004712116198193_cond
          L2InteropCommitmentTree.Common.for_2268004712116198193_post
          L2InteropCommitmentTree.Common.for_2268004712116198193_body) (Ok evm σ)
        = Ok (updateWalk 0 2 k evm i idx maxN cur).1 σ'
      ∧ (Ok (updateWalk 0 2 k evm i idx maxN cur).1 σ')["var_currentHash"]!!
          = (updateWalk 0 2 k evm i idx maxN cur).2.2.2.2 := by
  intro k
  induction k with
  | zero =>
    intro fuel evm σ i idx maxN cur hi hidx hmax hcur hk _ _ hfuel
    rcases fuel with _ | _ | f
    · omega
    · omega
    have hstop : ¬ (i < evm.sload 0) := by
      rw [Fin.lt_def]; omega
    rw [For']
    dsimp only
    unfold _root_.L2InteropCommitmentTree.Common.for_2268004712116198193_cond
    simp only [eval, Lit', mkOk_of_isOk (show isOk (Ok evm σ) from trivial)]
    rw [if_neg (by decide : ¬ ((1 : UInt256) = 0))]
    obtain ⟨fb, rfl⟩ : ∃ fb, f = fb + 1 := ⟨f - 1, by omega⟩
    rw [updateBody_break_5205 hi hstop]
    dsimp only
    refine ⟨Finmap.insert "split_expr_4" 0
      (Finmap.insert "split_expr_3" (evm.sload 0) σ), ?_, ?_⟩
    · rw [show (🧟 (Checkpoint (.Break evm (Finmap.insert "split_expr_4" 0
          (Finmap.insert "split_expr_3" (evm.sload 0) σ)))) : State)
        = Ok evm (Finmap.insert "split_expr_4" 0
            (Finmap.insert "split_expr_3" (evm.sload 0) σ)) from rfl]
      simp only [overwrite?_of_Ok]
      rfl
    · rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
      exact hcur
  | succ k ih =>
    intro fuel evm σ i idx maxN cur hi hidx hmax hcur hk hpass hssinv hfuel
    obtain ⟨fb, rfl⟩ : ∃ fb, fuel = fb + 1 + 1 + 1 := ⟨fuel - 3, by omega⟩
    have hcont : i < evm.sload 0 := by
      rw [Fin.lt_def]; omega
    have hi1 : i.val + 1 < 2 ^ 256 := by
      have := (evm.sload (0 : UInt256)).isLt
      have hs : UInt256.size = 2 ^ 256 := by norm_num
      omega
    -- unfold one For iteration; the guard `1` always enters
    rw [For']
    dsimp only
    unfold _root_.L2InteropCommitmentTree.Common.for_2268004712116198193_cond
    simp only [eval, Lit', mkOk_of_isOk (show isOk (Ok evm σ) from trivial)]
    rw [if_neg (by decide : ¬ ((1 : UInt256) = 0))]
    -- the pass conditions at the current level
    have hp0 := hpass 0 (by omega)
    simp only [WalkOK, updateWalk, PassOK] at hp0
    -- one body pass by parity/edge
    have hbody :
        ∃ bs : VarStore,
          exec (fb+1) (.Block L2InteropCommitmentTree.Common.for_2268004712116198193_body)
              (Ok evm σ)
            = Ok (updateStep evm 0 2 i idx maxN cur).2 bs
          ∧ (Ok (updateStep evm 0 2 i idx maxN cur).2 bs)["var_i"]!! = i
          ∧ (Ok (updateStep evm 0 2 i idx maxN cur).2 bs)["var_index"]!!
              = Fin.shiftRight idx 1
          ∧ (Ok (updateStep evm 0 2 i idx maxN cur).2 bs)["var_maxNodeNumber"]!!
              = Fin.shiftRight maxN 1
          ∧ (Ok (updateStep evm 0 2 i idx maxN cur).2 bs)["var_currentHash"]!!
              = (updateStep evm 0 2 i idx maxN cur).1 := by
      by_cases hpar : Fin.land idx 1 = 0
      · by_cases hedge : maxN = idx
        · -- edge
          rw [if_pos hpar, if_pos hedge] at hp0
          have hbe := hp0.2.1
          have hb3 := hp0.2.2.1
          have hb4 := hp0.2.2.2
          have hstep : updateStep evm 0 2 i idx maxN cur = stepEdge evm 0 2 i idx cur := by
            unfold updateStep; rw [if_pos hpar, if_pos hedge]
          rw [hstep]
          rw [updateBody_edge_5205 hi hidx hmax hcur hcont hpar hedge hbe hp0.1 hb3 hb4]
          refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
          · exact (by
          rw [lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_ok_evm (e' := evm)]
          exact hi)
          · exact (by
          rw [lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide)]
          exact lookup_insert_self_fin)
          · exact (by
          rw [lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide)]
          exact lookup_insert_self_fin)
          · exact (by
          rw [lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide)]
          exact lookup_insert_self_fin)
        · -- even (non-edge)
          rw [if_pos hpar, if_neg hedge] at hp0
          have hstep : updateStep evm 0 2 i idx maxN cur
              = stepEven evm 2 i idx cur := by
            unfold updateStep; rw [if_pos hpar, if_neg hedge]
          rw [hstep]
          rw [updateBody_even_5205 hi hidx hmax hcur hcont hpar hedge hp0.2.1
              hp0.2.2.1 hp0.2.2.2.1 hp0.1 hp0.2.2.2.2.1 hp0.2.2.2.2.2]
          refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
          · exact (by
          rw [lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_ok_evm (e' := evm)]
          exact hi)
          · exact (by
          rw [lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide)]
          exact lookup_insert_self_fin)
          · exact (by
          rw [lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide)]
          exact lookup_insert_self_fin)
          · exact (by
          rw [lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide)]
          exact lookup_insert_self_fin)
      · -- odd
        rw [if_neg hpar] at hp0
        have hstep : updateStep evm 0 2 i idx maxN cur
            = stepOdd evm 2 i idx cur := by
          unfold updateStep; rw [if_neg hpar]
        rw [hstep]
        rw [updateBody_odd_5205 hi hidx hmax hcur hcont hpar hp0.2.1 hp0.2.2.1
          hp0.1 hp0.2.2.2.1 hp0.2.2.2.2]
        refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
        · exact (by
        rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_ok_evm (e' := evm)]
        exact hi)
        · exact (by
        rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
        · exact (by
        rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
        · exact (by
        rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    -- compose: revive, post, recurse via ih
    obtain ⟨bs, hexec, hbi, hbidx, hbmax, hbcur⟩ := hbody
    rw [hexec]
    dsimp only
    rw [reviveJump_of_isOk
      (show isOk (Ok (updateStep evm 0 2 i idx maxN cur).2 bs) from trivial)]
    have hpost : exec (fb+1) (.Block L2InteropCommitmentTree.Common.for_2268004712116198193_post)
        (Ok (updateStep evm 0 2 i idx maxN cur).2 bs)
        = Ok (updateStep evm 0 2 i idx maxN cur).2 (bs.insert "var_i" (i + 1)) := by
      unfold _root_.L2InteropCommitmentTree.Common.for_2268004712116198193_post
      simp only [cons, nil, AssignPrimCall', evalArgs, evalTail, cons', head',
                 reverse', multifill', PrimCall', Lit', Var', execPrimCall,
                 evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
                 List.singleton_append, EVMAdd', multifill_cons, multifill_nil]
      rw [hbi]
      rfl
    rw [hpost]
    simp only [overwrite?_of_Ok]
    have hs : UInt256.size = 2 ^ 256 := by norm_num
    have hi1v : (i + 1).val = i.val + 1 := by
      rw [Fin.val_add, show ((1 : UInt256)).val = 1 from by decide]
      exact Nat.mod_eq_of_lt (by omega)
    have hw1 : (updateWalk 0 2 1 evm i idx maxN cur).1
        = (updateStep evm 0 2 i idx maxN cur).2 := by
      simp only [updateWalk]
    have hssStep : ((updateStep evm 0 2 i idx maxN cur).2).sload 0 = evm.sload 0 := by
      rw [← hw1]
      exact hssinv 1 (by omega)
    obtain ⟨σ', hσ'⟩ := ih (fuel := fb+1)
      (evm := (updateStep evm 0 2 i idx maxN cur).2)
      (σ := bs.insert "var_i" (i + 1))
      (i := i + 1) (idx := Fin.shiftRight idx 1)
      (maxN := Fin.shiftRight maxN 1) (cur := (updateStep evm 0 2 i idx maxN cur).1)
      (by exact lookup_insert_self_fin)
      (by rw [lookup_insert_ne_fin (by decide)]; exact hbidx)
      (by rw [lookup_insert_ne_fin (by decide)]; exact hbmax)
      (by rw [lookup_insert_ne_fin (by decide)]; exact hbcur)
      (by rw [hi1v, hssStep]; omega)
      (by intro j hj
          have := hpass (j+1) (by omega)
          simpa only [updateWalk] using this)
      (by intro j hj
          have h1 := hssinv (j+1) (by omega)
          have h2 : (updateWalk 0 2 (j+1) evm i idx maxN cur).1
              = (updateWalk 0 2 j (updateStep evm 0 2 i idx maxN cur).2 (i+1)
                  (Fin.shiftRight idx 1) (Fin.shiftRight maxN 1)
                  (updateStep evm 0 2 i idx maxN cur).1).1 := by
            simp only [updateWalk]
          rw [← h2, h1, hssStep])
      (by omega)
    have hwstep : updateWalk 0 2 (k+1) evm i idx maxN cur
        = updateWalk 0 2 k (updateStep evm 0 2 i idx maxN cur).2 (i+1)
            (Fin.shiftRight idx 1) (Fin.shiftRight maxN 1)
            (updateStep evm 0 2 i idx maxN cur).1 := by
      simp only [updateWalk]
    refine ⟨σ', ?_, ?_⟩
    · try simp only [overwrite?_of_Ok]
      rw [hwstep]
      exact hσ'.1
    · rw [hwstep]
      exact hσ'.2

/-! ## The `fun_updateLeaf_5205` top-level closed form -/

/-- The leaf-write block of `fun_updateLeaf_5205` (slot 2 hardwired):
stores the new leaf hash at element `idx` of the level-0 array and
initializes `var_currentHash` and `var_i`. -/
private lemma leafWrite5205_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {idx leaf : Literal}
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hleaf : (Ok evm σ)["var_itemHash"]!! = leaf)
    (hne : evm.sload 2 ≠ 0)
    (hb : idx < (arrOut evm 2).2.sload (arrOut evm 2).1) :
    exec (fuel+1) (.Block
        [LetCall ["_1", "_2"] storage_array_index_access_bytes32_dyn_ptr_5303 [Lit 2],
         LetCall ["_3", "_4"] storage_array_index_access_bytes32_dyn_ptr
           [Var "_1", Var "var_index"],
         ExprStmtCall update_storage_value_bytes32_to_bytes32
           [Var "_3", Var "_4", Var "var_itemHash"],
         LetEq "var_currentHash" (Var "var_itemHash"),
         LetEq "var_i" (Lit 0)]) (Ok evm σ)
      = Ok (leafWriteEvm evm 0 idx leaf)
          (Finmap.insert "var_i" 0
            (Finmap.insert "var_currentHash" leaf
              (Finmap.insert "_3"
                  ((arrOut (arrOut evm 2).2 (arrOut evm 2).1).1 + idx)
                (Finmap.insert "_4" 0
                  (Finmap.insert "_1" (arrOut evm 2).1
                    (Finmap.insert "_2" 0 σ)))))) := by
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  have hleafe : ∀ e : EVMState, (Ok e σ)["var_itemHash"]!! = leaf := fun _ => hleaf
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [storage_array_index0_ptr_call hne]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hidxe]
  rw [storage_array_index_ptr_call hb]
  rw [cons, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hleafe]
  rw [update_storage_call_0]
  rw [cons, LetEq']
  simp only [Var']
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hleafe]
  simp only [insert_Ok]
  rw [cons, nil, LetEq']
  simp only [Lit', insert_Ok]
  rfl

/-- The counter block `{ var_i := 0 }`. -/
private lemma vari5205_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} :
    exec (fuel+1) (.Block [Assign "var_i" (Lit 0)]) (Ok evm σ)
      = Ok evm (Finmap.insert "var_i" 0 σ) := by
  rw [cons, nil, Assign']
  simp only [Lit', eval, insert_Ok]

/-- **CLOSED FORM OF `fun_updateLeaf_5205`** (self slot 0).  Success path: the
guard passes (`idx ≤ sload(1) − 1`), the new leaf hash is stored at position
`idx` of level 0 (nodes array at slot 2), the Merkle path is recomputed level
by level (`updateWalk` at `ss := 0`, `base := 2`), and the new root is
returned. -/
theorem updateLeaf_5205_call
    {evm : EVMState} {store : VarStore} {fuel k : ℕ}
    {idx leaf : Literal} {v : Identifier}
    (hsub0 : evm.sload 1 ≠ 0)
    (hle : ¬ (idx > evm.sload 1 - 1))
    (hne2 : evm.sload 2 ≠ 0)
    (hbidx : idx < (arrOut evm 2).2.sload (arrOut evm 2).1)
    (hk : ((leafWriteEvm evm 0 idx leaf).sload 0).val = k)
    (hpass : ∀ j, j < k → WalkOK 0 2
        (updateWalk 0 2 j (leafWriteEvm evm 0 idx leaf) 0 idx
          (evm.sload 1 - 1) leaf))
    (hssinv : ∀ j, j ≤ k →
        ((updateWalk 0 2 j (leafWriteEvm evm 0 idx leaf) 0 idx
            (evm.sload 1 - 1) leaf).1).sload 0
          = (leafWriteEvm evm 0 idx leaf).sload 0)
    (hfuel : 2 * k + 2 ≤ fuel) :
    execCall (fuel+1) fun_updateLeaf_5205 [v] (Ok evm store, [idx, leaf])
      = Ok (updateWalk 0 2 k (leafWriteEvm evm 0 idx leaf) 0 idx
            (evm.sload 1 - 1) leaf).1
          (store.insert v
            (updateWalk 0 2 k (leafWriteEvm evm 0 idx leaf) 0 idx
              (evm.sload 1 - 1) leaf).2.2.2.2) := by
  unfold execCall call fun_updateLeaf_5205
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  set s0 := (Ok evm store)☎️⟦["var_index", "var_itemHash"], [idx, leaf]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["var_index"]!! = idx := by rw [hs0]; exact lookup_initcall_1
  have hp2 : s0["var_itemHash"]!! = leaf := by
    rw [hs0]; exact lookup_initcall_2 (by decide)
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq] at hp1 hp2 ⊢
  have hp1e : ∀ e : EVMState, (Ok e σ0)["var_index"]!! = idx := fun _ => hp1
  have hp2e : ∀ e : EVMState, (Ok e σ0)["var_itemHash"]!! = leaf := fun _ => hp2
  -- statement 1: split_expr_0 := sload(1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  -- statement 2: var_maxNodeNumber := checked_sub(split_expr_0)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [checked_sub_call hsub0]
  -- statement 3: the range guard is skipped
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMGt']
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hp1]
  rw [lookup_insert_self_fin]
  rw [show fromBool (idx > evm.sload 1 - 1) = (0 : UInt256) from by
    rw [decide_eq_false hle]; rfl]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- statement 4: the leaf write
  rw [cons]
  rw [leafWrite5205_block (idx := idx) (leaf := leaf)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact hp1)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact hp2)
    hne2 hbidx]
  -- statement 5: the counter block
  rw [cons]
  rw [vari5205_block]
  -- statement 6: the For loop — fold the inline AST to the named defs
  rw [cons]
  rw [show ([AssignPrimCall ["var_i"] .Add [Var "var_i", Lit 1]] : List Stmt)
        = _root_.L2InteropCommitmentTree.Common.for_2268004712116198193_post from rfl,
      show ([LetPrimCall ["split_expr_3"] .Sload [Lit 0],
             LetPrimCall ["split_expr_4"] .Lt [Var "var_i", Var "split_expr_3"],
             If (PrimCall .Iszero [Var "split_expr_4"]) [Stmt.Break],
             LetCall ["split_expr_5"] mod_uint256 [Var "var_index"],
             Switch (PrimCall .Iszero [Var "split_expr_5"])
               [(0, [.Block
                      [LetCall ["_5", "_6"] storage_array_index_access_bytes32_dyn_ptr
                         [Lit 2, Var "var_i"],
                       LetCall ["split_expr_6"] checked_sub_uint256 [Var "var_index"],
                       LetCall ["_7", "_8"] storage_array_index_access_bytes32_dyn_ptr
                         [Var "_5", Var "split_expr_6"],
                       LetPrimCall ["split_expr_7"] .Sload [Var "_7"],
                       LetCall ["split_expr_8"] extract_from_storage_value_dynamict_bytes32
                         [Var "split_expr_7", Var "_8"]],
                     .Block
                      [AssignCall ["var_currentHash"] fun_efficientHash
                         [Var "split_expr_8", Var "var_currentHash"]]])]
               [LetEq "expr" (Lit 0),
                Switch (PrimCall .Eq [Var "var_maxNodeNumber", Var "var_index"])
                  [(0, [LetCall ["_9", "_10"] storage_array_index_access_bytes32_dyn_ptr
                          [Lit 2, Var "var_i"],
                        LetCall ["split_expr_9"] checked_add_uint256 [Var "var_index"],
                        LetCall ["_11", "_12"] storage_array_index_access_bytes32_dyn_ptr
                          [Var "_9", Var "split_expr_9"],
                        LetPrimCall ["split_expr_10"] .Sload [Var "_11"],
                        AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
                          [Var "split_expr_10", Var "_12"]])]
                  [LetCall ["_13", "_14"] storage_array_index_access_bytes32_dyn_ptr
                     [Lit 3, Var "var_i"],
                   LetPrimCall ["split_expr_11"] .Sload [Var "_13"],
                   AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
                     [Var "split_expr_11", Var "_14"]],
                AssignCall ["var_currentHash"] fun_efficientHash
                  [Var "var_currentHash", Var "expr"]],
             .Block
              [AssignCall ["var_index"] checked_div_uint256 [Var "var_index"],
               AssignCall ["var_maxNodeNumber"] checked_div_uint256 [Var "var_maxNodeNumber"],
               LetCall ["split_expr_12"] checked_add_uint256 [Var "var_i"],
               LetCall ["_15", "_16"] storage_array_index_access_bytes32_dyn_ptr
                 [Lit 2, Var "split_expr_12"],
               LetCall ["_17", "_18"] storage_array_index_access_bytes32_dyn_ptr
                 [Var "_15", Var "var_index"]],
             .Block
              [ExprStmtCall update_storage_value_bytes32_to_bytes32
                 [Var "_17", Var "_18", Var "var_currentHash"]]] : List Stmt)
        = _root_.L2InteropCommitmentTree.Common.for_2268004712116198193_body from rfl,
      show (Lit 1 : Expr)
        = _root_.L2InteropCommitmentTree.Common.for_2268004712116198193_cond from rfl]
  obtain ⟨σ', hσ'eq, hσ'cur⟩ := update_loop_5205 k (fuel := fuel+1)
    (evm := leafWriteEvm evm 0 idx leaf)
    (σ := Finmap.insert "var_i" 0 (Finmap.insert "var_i" 0
      (Finmap.insert "var_currentHash" leaf
        (Finmap.insert "_3"
            ((arrOut (arrOut evm 2).2 (arrOut evm 2).1).1 + idx)
          (Finmap.insert "_4" 0
            (Finmap.insert "_1" (arrOut evm 2).1
              (Finmap.insert "_2" 0
                (Finmap.insert "var_maxNodeNumber" (evm.sload 1 - 1)
                  (Finmap.insert "split_expr_0" (evm.sload 1) σ0)))))))))
    (i := 0) (idx := idx)
    (maxN := evm.sload 1 - 1) (cur := leaf)
    (by exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hp1e _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_self_fin])
    (by rw [show ((0 : UInt256)).val = 0 from by decide]; omega)
    hpass hssinv (by omega)
  rw [hσ'eq]
  -- statement 7: var := var_currentHash
  rw [cons, nil, Assign']
  simp only [Var']
  rw [hσ'cur]
  -- rets [var] + call wrapper
  rw [lookup_insert' (by trivial)]
  rw [reviveJump_of_isOk (by rw [isOk_insert]; trivial)]
  try simp only [overwrite?_of_Ok]
  rw [insert_Ok]
  rw [setStore_ok]
  try simp only [multifill_cons, multifill_nil, insert_Ok]

/-- **`fun_updateLeaf_5205`, call level** (pair form): the same closed form as
`updateLeaf_5205_call`, but at the `call` level consumed by expression-position
evaluation (`evalCall = head' ∘ call`, as in `pop(fun_updateLeaf_5205(...))`).
The restored caller state carries the walk's evm over the caller's store, and
the single return value is the recomputed root. -/
theorem updateLeaf_5205_vcall
    {evm : EVMState} {store : VarStore} {fuel k : ℕ}
    {idx leaf : Literal}
    (hsub0 : evm.sload 1 ≠ 0)
    (hle : ¬ (idx > evm.sload 1 - 1))
    (hne2 : evm.sload 2 ≠ 0)
    (hbidx : idx < (arrOut evm 2).2.sload (arrOut evm 2).1)
    (hk : ((leafWriteEvm evm 0 idx leaf).sload 0).val = k)
    (hpass : ∀ j, j < k → WalkOK 0 2
        (updateWalk 0 2 j (leafWriteEvm evm 0 idx leaf) 0 idx
          (evm.sload 1 - 1) leaf))
    (hssinv : ∀ j, j ≤ k →
        ((updateWalk 0 2 j (leafWriteEvm evm 0 idx leaf) 0 idx
            (evm.sload 1 - 1) leaf).1).sload 0
          = (leafWriteEvm evm 0 idx leaf).sload 0)
    (hfuel : 2 * k + 2 ≤ fuel) :
    call (fuel+1) [idx, leaf] fun_updateLeaf_5205 (Ok evm store)
      = (Ok (updateWalk 0 2 k (leafWriteEvm evm 0 idx leaf) 0 idx
            (evm.sload 1 - 1) leaf).1 store,
         [(updateWalk 0 2 k (leafWriteEvm evm 0 idx leaf) 0 idx
            (evm.sload 1 - 1) leaf).2.2.2.2]) := by
  unfold call fun_updateLeaf_5205
  simp only [params, body, rets, mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  set s0 := (Ok evm store)☎️⟦["var_index", "var_itemHash"], [idx, leaf]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["var_index"]!! = idx := by rw [hs0]; exact lookup_initcall_1
  have hp2 : s0["var_itemHash"]!! = leaf := by
    rw [hs0]; exact lookup_initcall_2 (by decide)
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq] at hp1 hp2 ⊢
  have hp1e : ∀ e : EVMState, (Ok e σ0)["var_index"]!! = idx := fun _ => hp1
  have hp2e : ∀ e : EVMState, (Ok e σ0)["var_itemHash"]!! = leaf := fun _ => hp2
  -- statement 1: split_expr_0 := sload(1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  -- statement 2: var_maxNodeNumber := checked_sub(split_expr_0)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [checked_sub_call hsub0]
  -- statement 3: the range guard is skipped
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMGt']
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hp1]
  rw [lookup_insert_self_fin]
  rw [show fromBool (idx > evm.sload 1 - 1) = (0 : UInt256) from by
    rw [decide_eq_false hle]; rfl]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- statement 4: the leaf write
  rw [cons]
  rw [leafWrite5205_block (idx := idx) (leaf := leaf)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact hp1)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact hp2)
    hne2 hbidx]
  -- statement 5: the counter block
  rw [cons]
  rw [vari5205_block]
  -- statement 6: the For loop — fold the inline AST to the named defs
  rw [cons]
  rw [show ([AssignPrimCall ["var_i"] .Add [Var "var_i", Lit 1]] : List Stmt)
        = _root_.L2InteropCommitmentTree.Common.for_2268004712116198193_post from rfl,
      show ([LetPrimCall ["split_expr_3"] .Sload [Lit 0],
             LetPrimCall ["split_expr_4"] .Lt [Var "var_i", Var "split_expr_3"],
             If (PrimCall .Iszero [Var "split_expr_4"]) [Stmt.Break],
             LetCall ["split_expr_5"] mod_uint256 [Var "var_index"],
             Switch (PrimCall .Iszero [Var "split_expr_5"])
               [(0, [.Block
                      [LetCall ["_5", "_6"] storage_array_index_access_bytes32_dyn_ptr
                         [Lit 2, Var "var_i"],
                       LetCall ["split_expr_6"] checked_sub_uint256 [Var "var_index"],
                       LetCall ["_7", "_8"] storage_array_index_access_bytes32_dyn_ptr
                         [Var "_5", Var "split_expr_6"],
                       LetPrimCall ["split_expr_7"] .Sload [Var "_7"],
                       LetCall ["split_expr_8"] extract_from_storage_value_dynamict_bytes32
                         [Var "split_expr_7", Var "_8"]],
                     .Block
                      [AssignCall ["var_currentHash"] fun_efficientHash
                         [Var "split_expr_8", Var "var_currentHash"]]])]
               [LetEq "expr" (Lit 0),
                Switch (PrimCall .Eq [Var "var_maxNodeNumber", Var "var_index"])
                  [(0, [LetCall ["_9", "_10"] storage_array_index_access_bytes32_dyn_ptr
                          [Lit 2, Var "var_i"],
                        LetCall ["split_expr_9"] checked_add_uint256 [Var "var_index"],
                        LetCall ["_11", "_12"] storage_array_index_access_bytes32_dyn_ptr
                          [Var "_9", Var "split_expr_9"],
                        LetPrimCall ["split_expr_10"] .Sload [Var "_11"],
                        AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
                          [Var "split_expr_10", Var "_12"]])]
                  [LetCall ["_13", "_14"] storage_array_index_access_bytes32_dyn_ptr
                     [Lit 3, Var "var_i"],
                   LetPrimCall ["split_expr_11"] .Sload [Var "_13"],
                   AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
                     [Var "split_expr_11", Var "_14"]],
                AssignCall ["var_currentHash"] fun_efficientHash
                  [Var "var_currentHash", Var "expr"]],
             .Block
              [AssignCall ["var_index"] checked_div_uint256 [Var "var_index"],
               AssignCall ["var_maxNodeNumber"] checked_div_uint256 [Var "var_maxNodeNumber"],
               LetCall ["split_expr_12"] checked_add_uint256 [Var "var_i"],
               LetCall ["_15", "_16"] storage_array_index_access_bytes32_dyn_ptr
                 [Lit 2, Var "split_expr_12"],
               LetCall ["_17", "_18"] storage_array_index_access_bytes32_dyn_ptr
                 [Var "_15", Var "var_index"]],
             .Block
              [ExprStmtCall update_storage_value_bytes32_to_bytes32
                 [Var "_17", Var "_18", Var "var_currentHash"]]] : List Stmt)
        = _root_.L2InteropCommitmentTree.Common.for_2268004712116198193_body from rfl,
      show (Lit 1 : Expr)
        = _root_.L2InteropCommitmentTree.Common.for_2268004712116198193_cond from rfl]
  obtain ⟨σ', hσ'eq, hσ'cur⟩ := update_loop_5205 k (fuel := fuel+1)
    (evm := leafWriteEvm evm 0 idx leaf)
    (σ := Finmap.insert "var_i" 0 (Finmap.insert "var_i" 0
      (Finmap.insert "var_currentHash" leaf
        (Finmap.insert "_3"
            ((arrOut (arrOut evm 2).2 (arrOut evm 2).1).1 + idx)
          (Finmap.insert "_4" 0
            (Finmap.insert "_1" (arrOut evm 2).1
              (Finmap.insert "_2" 0
                (Finmap.insert "var_maxNodeNumber" (evm.sload 1 - 1)
                  (Finmap.insert "split_expr_0" (evm.sload 1) σ0)))))))))
    (i := 0) (idx := idx)
    (maxN := evm.sload 1 - 1) (cur := leaf)
    (by exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hp1e _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_self_fin])
    (by rw [show ((0 : UInt256)).val = 0 from by decide]; omega)
    hpass hssinv (by omega)
  rw [hσ'eq]
  -- statement 7: var := var_currentHash
  rw [cons, nil, Assign']
  simp only [Var']
  rw [hσ'cur]
  -- rets [var] + call wrapper (pair form: no multifill)
  rw [lookup_insert' (by trivial)]
  rw [reviveJump_of_isOk (by rw [isOk_insert]; trivial)]
  try simp only [overwrite?_of_Ok]
  rw [insert_Ok]
  rw [setStore_ok]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
