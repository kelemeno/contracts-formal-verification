import Clear.ReasoningPrinciple
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr_5303

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_4843491680166179088
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_storage_atoms_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_hash_user
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn_5278
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_updateLeaf

/-
  U3 — the `fun_updateLeaf` loop as a pure storage fold.

  Each loop level reads the sibling (odd / even / edge), hashes the pair
  (`accOut`), and stores the parent node at level `i+1`, element `idx >> 1`.
  `stepOdd`/`stepEven`/`stepEdge` are the pure per-level effects;
  `updateBody_*` prove one body pass equals one step (composed from the U2
  chunk closed forms).  The loop lemma (U3b) then iterates them.

  Axiom-free.
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

private lemma primCall_keccakOut {s : State} {a b : Literal} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (keccakOut s.evm a b).2, [(keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

/-- The parent-store evm effect: two `arrOut` slot computations then the
`sstore` of `v` at element `j` of the level-`l` array. -/
def nodeStore (σ : EVMState) (base l j v : UInt256) : EVMState :=
  (arrOut (arrOut σ base).2 ((arrOut σ base).1 + l)).2.sstore
    ((arrOut (arrOut σ base).2 ((arrOut σ base).1 + l)).1 + j) v

/-- One odd-index loop level: read the left sibling at `idx − 1`, hash
`H(sib ‖ cur)`, store the parent. Returns `(newCur, evm')`. -/
def stepOdd (σ : EVMState) (base i idx cur : UInt256) : UInt256 × EVMState :=
  ((accOut (sibRead σ base i (idx - 1)).2 (sibRead σ base i (idx - 1)).1 cur).1,
   nodeStore (accOut (sibRead σ base i (idx - 1)).2 (sibRead σ base i (idx - 1)).1 cur).2
     base (i + 1) (Fin.shiftRight idx 1)
     (accOut (sibRead σ base i (idx - 1)).2 (sibRead σ base i (idx - 1)).1 cur).1)

/-- The odd switch arm: sibling read then hash — over a generic state. -/
private lemma arm_odd
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {base i idx cur : Literal}
    (h1 : (Ok evm σ)["_1"]!! = base)
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur)
    (hidx0 : idx ≠ 0)
    (hb1 : i < evm.sload base)
    (hb2 : idx - 1 < (arrOut evm base).2.sload ((arrOut evm base).1 + i)) :
    exec (fuel+1) (.Block
        [.Block
          [LetCall ["_6", "_7"] storage_array_index_access_bytes32_dyn__dyn
             [Var "_1", Var "var_i"],
           LetCall ["split_expr_7"] checked_sub_uint256 [Var "var_index"],
           LetCall ["_8", "_9"] storage_array_index_access_bytes32_dyn__dyn
             [Var "_6", Var "split_expr_7"],
           LetPrimCall ["split_expr_8"] .Sload [Var "_8"],
           LetCall ["split_expr_9"] extract_from_storage_value_dynamict_bytes32
             [Var "split_expr_8", Var "_9"]],
         .Block
          [AssignCall ["var_currentHash"] fun_efficientHash
             [Var "split_expr_9", Var "var_currentHash"]]]) (Ok evm σ)
      = Ok (accOut (sibRead evm base i (idx - 1)).2 (sibRead evm base i (idx - 1)).1 cur).2
          (Finmap.insert "var_currentHash"
              (accOut (sibRead evm base i (idx - 1)).2 (sibRead evm base i (idx - 1)).1 cur).1
            (Finmap.insert "split_expr_9" (sibRead evm base i (idx - 1)).1
              (Finmap.insert "split_expr_8" (sibRead evm base i (idx - 1)).1
                (Finmap.insert "_8"
                    ((arrOut (arrOut evm base).2 ((arrOut evm base).1 + i)).1 + (idx - 1))
                  (Finmap.insert "_9" 0
                    (Finmap.insert "split_expr_7" (idx - 1)
                      (Finmap.insert "_6" ((arrOut evm base).1 + i)
                        (Finmap.insert "_7" 0 σ)))))))) := by
  have hcure : ∀ e : EVMState, (Ok e σ)["var_currentHash"]!! = cur := fun _ => hcur
  rw [cons]
  rw [oddRead_block h1 hi hidx hidx0 hb1 hb2]
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

/-- **One odd-index body pass** of the `updateLeaf` loop equals `stepOdd`:
break-check passes, the odd switch arm reads the left sibling and hashes, the
tail halves the indices and stores the parent node. -/
lemma updateBody_odd
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    {ss base i idx maxN cur : Literal}
    (hss : (Ok evm σ)["var_self_slot"]!! = ss)
    (h1 : (Ok evm σ)["_1"]!! = base)
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hmax : (Ok evm σ)["var_maxNodeNumber"]!! = maxN)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur)
    (hbreak : i < evm.sload ss)
    (hodd : Fin.land idx 1 ≠ 0)
    (hb1 : i < evm.sload base)
    (hb2 : idx - 1 < (arrOut evm base).2.sload ((arrOut evm base).1 + i))
    (haddl : i.val + 1 < 2 ^ 256)
    (hb3 : i + 1
      < (accOut (sibRead evm base i (idx - 1)).2 (sibRead evm base i (idx - 1)).1 cur).2.sload base)
    (hb4 : Fin.shiftRight idx 1
      < (arrOut (accOut (sibRead evm base i (idx - 1)).2 (sibRead evm base i (idx - 1)).1 cur).2
            base).2.sload
          ((arrOut (accOut (sibRead evm base i (idx - 1)).2 (sibRead evm base i (idx - 1)).1 cur).2
              base).1 + (i + 1))) :
    exec (fuel+1) (.Block L2InteropCommitmentTree.Common.for_4843491680166179088_body)
        (Ok evm σ)
      = Ok (stepOdd evm base i idx cur).2
          (Finmap.insert "_18"
              ((arrOut (arrOut (accOut (sibRead evm base i (idx - 1)).2
                    (sibRead evm base i (idx - 1)).1 cur).2 base).2
                  ((arrOut (accOut (sibRead evm base i (idx - 1)).2
                    (sibRead evm base i (idx - 1)).1 cur).2 base).1 + (i + 1))).1
                + Fin.shiftRight idx 1)
            (Finmap.insert "_19" 0
              (Finmap.insert "_16"
                  ((arrOut (accOut (sibRead evm base i (idx - 1)).2
                    (sibRead evm base i (idx - 1)).1 cur).2 base).1 + (i + 1))
                (Finmap.insert "_17" 0
                  (Finmap.insert "split_expr_14" (i + 1)
                    (Finmap.insert "var_maxNodeNumber" (Fin.shiftRight maxN 1)
                      (Finmap.insert "var_index" (Fin.shiftRight idx 1)
                        (Finmap.insert "var_currentHash" (stepOdd evm base i idx cur).1
                          (Finmap.insert "split_expr_9" (sibRead evm base i (idx - 1)).1
                            (Finmap.insert "split_expr_8" (sibRead evm base i (idx - 1)).1
                              (Finmap.insert "_8"
                                  ((arrOut (arrOut evm base).2 ((arrOut evm base).1 + i)).1
                                    + (idx - 1))
                                (Finmap.insert "_9" 0
                                  (Finmap.insert "split_expr_7" (idx - 1)
                                    (Finmap.insert "_6" ((arrOut evm base).1 + i)
                                      (Finmap.insert "_7" 0
                                        (Finmap.insert "split_expr_6" (Fin.land idx 1)
                                          (Finmap.insert "split_expr_5" 1
                                            (Finmap.insert "split_expr_4" (evm.sload ss)
                                              σ)))))))))))))))))) := by
  have hidx0 : idx ≠ 0 := by
    intro h
    exact hodd (by rw [h]; decide)
  have hsse : ∀ e : EVMState, (Ok e σ)["var_self_slot"]!! = ss := fun _ => hss
  have h1e : ∀ e : EVMState, (Ok e σ)["_1"]!! = base := fun _ => h1
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  have hmaxe : ∀ e : EVMState, (Ok e σ)["var_maxNodeNumber"]!! = maxN := fun _ => hmax
  have hcure : ∀ e : EVMState, (Ok e σ)["var_currentHash"]!! = cur := fun _ => hcur
  unfold _root_.L2InteropCommitmentTree.Common.for_4843491680166179088_body
  -- statement 1: split_expr_4 := sload(var_self_slot)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [hss]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  -- statement 2: split_expr_5 := lt(var_i, split_expr_4)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hie, lookup_insert_self_fin]
  rw [show fromBool (i < evm.sload ss) = (1 : UInt256) from by
    rw [decide_eq_true hbreak]; rfl]
  simp only [insert_Ok]
  -- statement 3: if iszero(split_expr_5) {break} — skipped
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- statement 4: split_expr_6 := mod_uint256(var_index)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hidxe]
  rw [mod2_call]
  simp only [insert_Ok]
  -- statement 5: the parity switch — scrutinee iszero(split_expr_6) = 0 (odd)
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
  rw [arm_odd (base := base) (i := i) (idx := idx) (cur := cur)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact h1e _)
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
  rw [divStore_prep_block (base := base) (lvl := i) (idx := idx) (maxN := maxN)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact h1e _)
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
  rw [store_call_block
    (by rw [lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_self_fin])]
  rfl


/-- One even-index (non-edge) loop level: read the right sibling at `idx + 1`,
hash `H(cur ‖ sib)`, store the parent. -/
def stepEven (σ : EVMState) (base i idx cur : UInt256) : UInt256 × EVMState :=
  ((accOut (sibRead σ base i (idx + 1)).2 cur (sibRead σ base i (idx + 1)).1).1,
   nodeStore (accOut (sibRead σ base i (idx + 1)).2 cur (sibRead σ base i (idx + 1)).1).2
     base (i + 1) (Fin.shiftRight idx 1)
     (accOut (sibRead σ base i (idx + 1)).2 cur (sibRead σ base i (idx + 1)).1).1)

/-- The even (non-edge) switch arm: zero `expr`, inner max-check switch selects
the sibling read at `idx + 1`, then hash `H(cur ‖ sib)`. -/
private lemma arm_even
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {base i idx maxN cur : Literal}
    (h1 : (Ok evm σ)["_1"]!! = base)
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hmax : (Ok evm σ)["var_maxNodeNumber"]!! = maxN)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur)
    (hne : maxN ≠ idx)
    (hadd : idx.val + 1 < 2 ^ 256)
    (hb1 : i < evm.sload base)
    (hb2 : idx + 1 < (arrOut evm base).2.sload ((arrOut evm base).1 + i)) :
    exec (fuel+1) (.Block
        [LetEq "expr" (Lit 0),
         Switch (PrimCall .Eq [Var "var_maxNodeNumber", Var "var_index"])
           [(0, [LetCall ["_10", "_11"] storage_array_index_access_bytes32_dyn__dyn
                   [Var "_1", Var "var_i"],
                 LetCall ["split_expr_10"] checked_add_uint256 [Var "var_index"],
                 LetCall ["_12", "_13"] storage_array_index_access_bytes32_dyn__dyn
                   [Var "_10", Var "split_expr_10"],
                 LetPrimCall ["split_expr_11"] .Sload [Var "_12"],
                 AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
                   [Var "split_expr_11", Var "_13"]])]
           [LetPrimCall ["split_expr_12"] .Add [Var "var_self_slot", Lit 3],
            LetCall ["_14", "_15"] storage_array_index_access_bytes32_dyn__dyn
              [Var "split_expr_12", Var "var_i"],
            LetPrimCall ["split_expr_13"] .Sload [Var "_14"],
            AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
              [Var "split_expr_13", Var "_15"]],
         AssignCall ["var_currentHash"] fun_efficientHash
           [Var "var_currentHash", Var "expr"]]) (Ok evm σ)
      = Ok (accOut (sibRead evm base i (idx + 1)).2 cur (sibRead evm base i (idx + 1)).1).2
          (Finmap.insert "var_currentHash"
              (accOut (sibRead evm base i (idx + 1)).2 cur (sibRead evm base i (idx + 1)).1).1
            (Finmap.insert "expr" (sibRead evm base i (idx + 1)).1
              (Finmap.insert "split_expr_11" (sibRead evm base i (idx + 1)).1
                (Finmap.insert "_12"
                    ((arrOut (arrOut evm base).2 ((arrOut evm base).1 + i)).1 + (idx + 1))
                  (Finmap.insert "_13" 0
                    (Finmap.insert "split_expr_10" (idx + 1)
                      (Finmap.insert "_10" ((arrOut evm base).1 + i)
                        (Finmap.insert "_11" 0
                          (Finmap.insert "expr" 0 σ))))))))) := by
  have h1e : ∀ e : EVMState, (Ok e σ)["_1"]!! = base := fun _ => h1
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
  rw [evenRead_block (base := base) (lvl := i) (idx := idx)
    (by rw [lookup_insert_ne_fin (by decide)]; exact h1e _)
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

/-- **One even-index (non-edge) body pass** equals `stepEven`. -/
lemma updateBody_even
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    {ss base i idx maxN cur : Literal}
    (hss : (Ok evm σ)["var_self_slot"]!! = ss)
    (h1 : (Ok evm σ)["_1"]!! = base)
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hmax : (Ok evm σ)["var_maxNodeNumber"]!! = maxN)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur)
    (hbreak : i < evm.sload ss)
    (heven : Fin.land idx 1 = 0)
    (hne : maxN ≠ idx)
    (hadd : idx.val + 1 < 2 ^ 256)
    (hb1 : i < evm.sload base)
    (hb2 : idx + 1 < (arrOut evm base).2.sload ((arrOut evm base).1 + i))
    (haddl : i.val + 1 < 2 ^ 256)
    (hb3 : i + 1
      < (accOut (sibRead evm base i (idx + 1)).2 cur (sibRead evm base i (idx + 1)).1).2.sload base)
    (hb4 : Fin.shiftRight idx 1
      < (arrOut (accOut (sibRead evm base i (idx + 1)).2 cur (sibRead evm base i (idx + 1)).1).2
            base).2.sload
          ((arrOut (accOut (sibRead evm base i (idx + 1)).2 cur (sibRead evm base i (idx + 1)).1).2
              base).1 + (i + 1))) :
    exec (fuel+1) (.Block L2InteropCommitmentTree.Common.for_4843491680166179088_body)
        (Ok evm σ)
      = Ok (stepEven evm base i idx cur).2
          (Finmap.insert "_18"
              ((arrOut (arrOut (accOut (sibRead evm base i (idx + 1)).2 cur
                    (sibRead evm base i (idx + 1)).1).2 base).2
                  ((arrOut (accOut (sibRead evm base i (idx + 1)).2 cur
                    (sibRead evm base i (idx + 1)).1).2 base).1 + (i + 1))).1
                + Fin.shiftRight idx 1)
            (Finmap.insert "_19" 0
              (Finmap.insert "_16"
                  ((arrOut (accOut (sibRead evm base i (idx + 1)).2 cur
                    (sibRead evm base i (idx + 1)).1).2 base).1 + (i + 1))
                (Finmap.insert "_17" 0
                  (Finmap.insert "split_expr_14" (i + 1)
                    (Finmap.insert "var_maxNodeNumber" (Fin.shiftRight maxN 1)
                      (Finmap.insert "var_index" (Fin.shiftRight idx 1)
                        (Finmap.insert "var_currentHash" (stepEven evm base i idx cur).1
                          (Finmap.insert "expr" (sibRead evm base i (idx + 1)).1
                            (Finmap.insert "split_expr_11" (sibRead evm base i (idx + 1)).1
                              (Finmap.insert "_12"
                                  ((arrOut (arrOut evm base).2 ((arrOut evm base).1 + i)).1
                                    + (idx + 1))
                                (Finmap.insert "_13" 0
                                  (Finmap.insert "split_expr_10" (idx + 1)
                                    (Finmap.insert "_10" ((arrOut evm base).1 + i)
                                      (Finmap.insert "_11" 0
                                        (Finmap.insert "expr" 0
                                          (Finmap.insert "split_expr_6" (Fin.land idx 1)
                                            (Finmap.insert "split_expr_5" 1
                                              (Finmap.insert "split_expr_4" (evm.sload ss)
                                                σ))))))))))))))))))) := by
  have hsse : ∀ e : EVMState, (Ok e σ)["var_self_slot"]!! = ss := fun _ => hss
  have h1e : ∀ e : EVMState, (Ok e σ)["_1"]!! = base := fun _ => h1
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  have hmaxe : ∀ e : EVMState, (Ok e σ)["var_maxNodeNumber"]!! = maxN := fun _ => hmax
  have hcure : ∀ e : EVMState, (Ok e σ)["var_currentHash"]!! = cur := fun _ => hcur
  unfold _root_.L2InteropCommitmentTree.Common.for_4843491680166179088_body
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [hss]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hie, lookup_insert_self_fin]
  rw [show fromBool (i < evm.sload ss) = (1 : UInt256) from by
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
  rw [arm_even (base := base) (i := i) (idx := idx) (maxN := maxN) (cur := cur)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact h1e _)
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
  rw [divStore_prep_block (base := base) (lvl := i) (idx := idx) (maxN := maxN)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact h1e _)
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
  rw [store_call_block
    (by rw [lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_self_fin])]
  rfl

/-- One edge loop level (`maxNodeNumber = index`): read the duplicated node
from the side array at `selfSlot + 3`, hash `H(cur ‖ sib)`, store the parent. -/
def stepEdge (σ : EVMState) (ss base i idx cur : UInt256) : UInt256 × EVMState :=
  ((accOut (sideRead σ (ss + 3) i).2 cur (sideRead σ (ss + 3) i).1).1,
   nodeStore (accOut (sideRead σ (ss + 3) i).2 cur (sideRead σ (ss + 3) i).1).2
     base (i + 1) (Fin.shiftRight idx 1)
     (accOut (sideRead σ (ss + 3) i).2 cur (sideRead σ (ss + 3) i).1).1)

/-- The edge switch arm: the inner max-check selects the side-array read. -/
private lemma arm_edge
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {ss i idx maxN cur : Literal}
    (hss : (Ok evm σ)["var_self_slot"]!! = ss)
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hmax : (Ok evm σ)["var_maxNodeNumber"]!! = maxN)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur)
    (heq : maxN = idx)
    (hbe : i < evm.sload (ss + 3)) :
    exec (fuel+1) (.Block
        [LetEq "expr" (Lit 0),
         Switch (PrimCall .Eq [Var "var_maxNodeNumber", Var "var_index"])
           [(0, [LetCall ["_10", "_11"] storage_array_index_access_bytes32_dyn__dyn
                   [Var "_1", Var "var_i"],
                 LetCall ["split_expr_10"] checked_add_uint256 [Var "var_index"],
                 LetCall ["_12", "_13"] storage_array_index_access_bytes32_dyn__dyn
                   [Var "_10", Var "split_expr_10"],
                 LetPrimCall ["split_expr_11"] .Sload [Var "_12"],
                 AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
                   [Var "split_expr_11", Var "_13"]])]
           [LetPrimCall ["split_expr_12"] .Add [Var "var_self_slot", Lit 3],
            LetCall ["_14", "_15"] storage_array_index_access_bytes32_dyn__dyn
              [Var "split_expr_12", Var "var_i"],
            LetPrimCall ["split_expr_13"] .Sload [Var "_14"],
            AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
              [Var "split_expr_13", Var "_15"]],
         AssignCall ["var_currentHash"] fun_efficientHash
           [Var "var_currentHash", Var "expr"]]) (Ok evm σ)
      = Ok (accOut (sideRead evm (ss + 3) i).2 cur (sideRead evm (ss + 3) i).1).2
          (Finmap.insert "var_currentHash"
              (accOut (sideRead evm (ss + 3) i).2 cur (sideRead evm (ss + 3) i).1).1
            (Finmap.insert "expr" (sideRead evm (ss + 3) i).1
              (Finmap.insert "split_expr_13" (sideRead evm (ss + 3) i).1
                (Finmap.insert "_14" ((arrOut evm (ss + 3)).1 + i)
                  (Finmap.insert "_15" 0
                    (Finmap.insert "split_expr_12" (ss + 3)
                      (Finmap.insert "expr" 0 σ))))))) := by
  have hsse : ∀ e : EVMState, (Ok e σ)["var_self_slot"]!! = ss := fun _ => hss
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
  rw [edgeRead_block (selfSlot := ss) (lvl := i)
    (by rw [lookup_insert_ne_fin (by decide)]; exact hsse _)
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
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
  rw [hcure]
  rw [lookup_insert_self_fin]
  rw [efficientHash_call_acc]
  try simp only [insert_Ok]

/-- **One edge body pass** (`maxNodeNumber = index`) equals `stepEdge`. -/
lemma updateBody_edge
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    {ss base i idx maxN cur : Literal}
    (hss : (Ok evm σ)["var_self_slot"]!! = ss)
    (h1 : (Ok evm σ)["_1"]!! = base)
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hmax : (Ok evm σ)["var_maxNodeNumber"]!! = maxN)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur)
    (hbreak : i < evm.sload ss)
    (heven : Fin.land idx 1 = 0)
    (heq : maxN = idx)
    (hbe : i < evm.sload (ss + 3))
    (haddl : i.val + 1 < 2 ^ 256)
    (hb3 : i + 1
      < (accOut (sideRead evm (ss + 3) i).2 cur (sideRead evm (ss + 3) i).1).2.sload base)
    (hb4 : Fin.shiftRight idx 1
      < (arrOut (accOut (sideRead evm (ss + 3) i).2 cur (sideRead evm (ss + 3) i).1).2
            base).2.sload
          ((arrOut (accOut (sideRead evm (ss + 3) i).2 cur (sideRead evm (ss + 3) i).1).2
              base).1 + (i + 1))) :
    exec (fuel+1) (.Block L2InteropCommitmentTree.Common.for_4843491680166179088_body)
        (Ok evm σ)
      = Ok (stepEdge evm ss base i idx cur).2
          (Finmap.insert "_18"
              ((arrOut (arrOut (accOut (sideRead evm (ss + 3) i).2 cur
                    (sideRead evm (ss + 3) i).1).2 base).2
                  ((arrOut (accOut (sideRead evm (ss + 3) i).2 cur
                    (sideRead evm (ss + 3) i).1).2 base).1 + (i + 1))).1
                + Fin.shiftRight idx 1)
            (Finmap.insert "_19" 0
              (Finmap.insert "_16"
                  ((arrOut (accOut (sideRead evm (ss + 3) i).2 cur
                    (sideRead evm (ss + 3) i).1).2 base).1 + (i + 1))
                (Finmap.insert "_17" 0
                  (Finmap.insert "split_expr_14" (i + 1)
                    (Finmap.insert "var_maxNodeNumber" (Fin.shiftRight maxN 1)
                      (Finmap.insert "var_index" (Fin.shiftRight idx 1)
                        (Finmap.insert "var_currentHash" (stepEdge evm ss base i idx cur).1
                          (Finmap.insert "expr" (sideRead evm (ss + 3) i).1
                            (Finmap.insert "split_expr_13" (sideRead evm (ss + 3) i).1
                              (Finmap.insert "_14" ((arrOut evm (ss + 3)).1 + i)
                                (Finmap.insert "_15" 0
                                  (Finmap.insert "split_expr_12" (ss + 3)
                                    (Finmap.insert "expr" 0
                                      (Finmap.insert "split_expr_6" (Fin.land idx 1)
                                        (Finmap.insert "split_expr_5" 1
                                          (Finmap.insert "split_expr_4" (evm.sload ss)
                                            σ))))))))))))))))) := by
  have hsse : ∀ e : EVMState, (Ok e σ)["var_self_slot"]!! = ss := fun _ => hss
  have h1e : ∀ e : EVMState, (Ok e σ)["_1"]!! = base := fun _ => h1
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  have hmaxe : ∀ e : EVMState, (Ok e σ)["var_maxNodeNumber"]!! = maxN := fun _ => hmax
  have hcure : ∀ e : EVMState, (Ok e σ)["var_currentHash"]!! = cur := fun _ => hcur
  unfold _root_.L2InteropCommitmentTree.Common.for_4843491680166179088_body
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [hss]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hie, lookup_insert_self_fin]
  rw [show fromBool (i < evm.sload ss) = (1 : UInt256) from by
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
  rw [arm_edge (ss := ss) (i := i) (idx := idx) (maxN := maxN) (cur := cur)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hsse _)
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
  rw [divStore_prep_block (base := base) (lvl := i) (idx := idx) (maxN := maxN)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact h1e _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact hie _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact hidxe _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact hmaxe _)
    haddl hb3 hb4]
  rw [cons, nil]
  rw [store_call_block
    (by rw [lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_self_fin])]
  rfl

/-! ## U3d — the loop as an iterated pure walk -/

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

/-- The per-level step, dispatching odd / even / edge. -/
def updateStep (σ : EVMState) (ss base i idx maxN cur : UInt256) : UInt256 × EVMState :=
  if Fin.land idx 1 = 0 then
    (if maxN = idx then stepEdge σ ss base i idx cur else stepEven σ base i idx cur)
  else stepOdd σ base i idx cur

/-- The full walk state after `j` levels: `(evm, i, idx, maxN, cur)`. -/
def updateWalk (ss base : UInt256) :
    ℕ → EVMState → UInt256 → UInt256 → UInt256 → UInt256
      → EVMState × UInt256 × UInt256 × UInt256 × UInt256
  | 0, σ, i, idx, maxN, cur => (σ, i, idx, maxN, cur)
  | (j+1), σ, i, idx, maxN, cur =>
      updateWalk ss base j (updateStep σ ss base i idx maxN cur).2 (i + 1)
        (Fin.shiftRight idx 1) (Fin.shiftRight maxN 1)
        (updateStep σ ss base i idx maxN cur).1

/-- **The break pass**: when the level counter has reached the level count,
the body breaks out immediately (only the two probe lets execute). -/
lemma updateBody_break
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {ss i : Literal}
    (hss : (Ok evm σ)["var_self_slot"]!! = ss)
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hstop : ¬ (i < evm.sload ss)) :
    exec (fuel+1) (.Block L2InteropCommitmentTree.Common.for_4843491680166179088_body)
        (Ok evm σ)
      = Checkpoint (.Break evm
          (Finmap.insert "split_expr_5" 0
            (Finmap.insert "split_expr_4" (evm.sload ss) σ))) := by
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  unfold _root_.L2InteropCommitmentTree.Common.for_4843491680166179088_body
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [hss]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hie, lookup_insert_self_fin]
  rw [show fromBool (i < evm.sload ss) = (0 : UInt256) from by
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

private lemma lookup_ok_evm {e e' : EVMState} {σ : VarStore} {k : Identifier} :
    (Ok e σ)[k]!! = (Ok e' σ)[k]!! := rfl

/-- The per-level side conditions (array bounds + no counter overflow) at a
walk state.  Dischargeable later from tree well-formedness + non-aliasing. -/
def PassOK (ss base : UInt256) (σe : EVMState) (i idx maxN cur : UInt256) : Prop :=
  i.val + 1 < 2 ^ 256 ∧
  (if Fin.land idx 1 = 0 then
    (if maxN = idx then
      i < σe.sload (ss + 3) ∧
      i + 1 < (accOut (sideRead σe (ss + 3) i).2 cur (sideRead σe (ss + 3) i).1).2.sload base ∧
      Fin.shiftRight idx 1
        < (arrOut (accOut (sideRead σe (ss + 3) i).2 cur (sideRead σe (ss + 3) i).1).2 base).2.sload
            ((arrOut (accOut (sideRead σe (ss + 3) i).2 cur
                (sideRead σe (ss + 3) i).1).2 base).1 + (i + 1))
    else
      idx.val + 1 < 2 ^ 256 ∧
      i < σe.sload base ∧
      idx + 1 < (arrOut σe base).2.sload ((arrOut σe base).1 + i) ∧
      i + 1 < (accOut (sibRead σe base i (idx + 1)).2 cur
          (sibRead σe base i (idx + 1)).1).2.sload base ∧
      Fin.shiftRight idx 1
        < (arrOut (accOut (sibRead σe base i (idx + 1)).2 cur
              (sibRead σe base i (idx + 1)).1).2 base).2.sload
            ((arrOut (accOut (sibRead σe base i (idx + 1)).2 cur
                (sibRead σe base i (idx + 1)).1).2 base).1 + (i + 1)))
  else
    (i < σe.sload base ∧
     idx - 1 < (arrOut σe base).2.sload ((arrOut σe base).1 + i) ∧
     i + 1 < (accOut (sibRead σe base i (idx - 1)).2
         (sibRead σe base i (idx - 1)).1 cur).2.sload base ∧
     Fin.shiftRight idx 1
       < (arrOut (accOut (sibRead σe base i (idx - 1)).2
             (sibRead σe base i (idx - 1)).1 cur).2 base).2.sload
           ((arrOut (accOut (sibRead σe base i (idx - 1)).2
               (sibRead σe base i (idx - 1)).1 cur).2 base).1 + (i + 1))))

/-- `PassOK` over a walk tuple. -/
def WalkOK (ss base : UInt256)
    (t : EVMState × UInt256 × UInt256 × UInt256 × UInt256) : Prop :=
  PassOK ss base t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2

/-- **U3e — THE `updateLeaf` LOOP IS THE PURE WALK.**  Under the per-level
bounds (`hwalk_pass`) and the level-count slot stability (`hwalk_ss`,
dischargeable by keccak/low-slot non-aliasing), the storage-side Merkle
update loop equals `updateWalk`: `k` levels of sibling-read + hash + parent
store, then the break. -/
lemma update_loop :
    ∀ (k : ℕ) {fuel : ℕ} {evm : EVMState} {σ : VarStore}
      {ss base i idx maxN cur : Literal},
    (Ok evm σ)["var_self_slot"]!! = ss →
    (Ok evm σ)["_1"]!! = base →
    (Ok evm σ)["var_i"]!! = i →
    (Ok evm σ)["var_index"]!! = idx →
    (Ok evm σ)["var_maxNodeNumber"]!! = maxN →
    (Ok evm σ)["var_currentHash"]!! = cur →
    i.val + k = (evm.sload ss).val →
    (∀ j, j < k → WalkOK ss base (updateWalk ss base j evm i idx maxN cur)) →
    (∀ j, j ≤ k → ((updateWalk ss base j evm i idx maxN cur).1).sload ss = evm.sload ss) →
    2 * k + 3 ≤ fuel →
    ∃ σ' : VarStore,
      exec fuel (.For L2InteropCommitmentTree.Common.for_4843491680166179088_cond
          L2InteropCommitmentTree.Common.for_4843491680166179088_post
          L2InteropCommitmentTree.Common.for_4843491680166179088_body) (Ok evm σ)
        = Ok (updateWalk ss base k evm i idx maxN cur).1 σ'
      ∧ (Ok (updateWalk ss base k evm i idx maxN cur).1 σ')["var_currentHash"]!!
          = (updateWalk ss base k evm i idx maxN cur).2.2.2.2 := by
  intro k
  induction k with
  | zero =>
    intro fuel evm σ ss base i idx maxN cur hss h1 hi hidx hmax hcur hk _ _ hfuel
    rcases fuel with _ | _ | f
    · omega
    · omega
    have hstop : ¬ (i < evm.sload ss) := by
      rw [Fin.lt_def]; omega
    rw [For']
    dsimp only
    unfold _root_.L2InteropCommitmentTree.Common.for_4843491680166179088_cond
    simp only [eval, Lit', mkOk_of_isOk (show isOk (Ok evm σ) from trivial)]
    rw [if_neg (by decide : ¬ ((1 : UInt256) = 0))]
    obtain ⟨fb, rfl⟩ : ∃ fb, f = fb + 1 := ⟨f - 1, by omega⟩
    rw [updateBody_break hss hi hstop]
    dsimp only
    refine ⟨Finmap.insert "split_expr_5" 0
      (Finmap.insert "split_expr_4" (evm.sload ss) σ), ?_, ?_⟩
    · rw [show (🧟 (Checkpoint (.Break evm (Finmap.insert "split_expr_5" 0
          (Finmap.insert "split_expr_4" (evm.sload ss) σ)))) : State)
        = Ok evm (Finmap.insert "split_expr_5" 0
            (Finmap.insert "split_expr_4" (evm.sload ss) σ)) from rfl]
      simp only [overwrite?_of_Ok]
      rfl
    · rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
      exact hcur
  | succ k ih =>
    intro fuel evm σ ss base i idx maxN cur hss h1 hi hidx hmax hcur hk hpass hssinv hfuel
    obtain ⟨fb, rfl⟩ : ∃ fb, fuel = fb + 1 + 1 + 1 := ⟨fuel - 3, by omega⟩
    have hcont : i < evm.sload ss := by
      rw [Fin.lt_def]; omega
    have hi1 : i.val + 1 < 2 ^ 256 := by
      have := (evm.sload ss).isLt
      have hs : UInt256.size = 2 ^ 256 := by norm_num
      omega
    -- unfold one For iteration; the guard `1` always enters
    rw [For']
    dsimp only
    unfold _root_.L2InteropCommitmentTree.Common.for_4843491680166179088_cond
    simp only [eval, Lit', mkOk_of_isOk (show isOk (Ok evm σ) from trivial)]
    rw [if_neg (by decide : ¬ ((1 : UInt256) = 0))]
    -- the pass conditions at the current level
    have hp0 := hpass 0 (by omega)
    simp only [WalkOK, updateWalk, PassOK] at hp0
    -- one body pass by parity/edge
    have hbody :
        ∃ bs : VarStore,
          exec (fb+1) (.Block L2InteropCommitmentTree.Common.for_4843491680166179088_body)
              (Ok evm σ)
            = Ok (updateStep evm ss base i idx maxN cur).2 bs
          ∧ (Ok (updateStep evm ss base i idx maxN cur).2 bs)["var_self_slot"]!! = ss
          ∧ (Ok (updateStep evm ss base i idx maxN cur).2 bs)["_1"]!! = base
          ∧ (Ok (updateStep evm ss base i idx maxN cur).2 bs)["var_i"]!! = i
          ∧ (Ok (updateStep evm ss base i idx maxN cur).2 bs)["var_index"]!!
              = Fin.shiftRight idx 1
          ∧ (Ok (updateStep evm ss base i idx maxN cur).2 bs)["var_maxNodeNumber"]!!
              = Fin.shiftRight maxN 1
          ∧ (Ok (updateStep evm ss base i idx maxN cur).2 bs)["var_currentHash"]!!
              = (updateStep evm ss base i idx maxN cur).1 := by
      by_cases hpar : Fin.land idx 1 = 0
      · by_cases hedge : maxN = idx
        · -- edge
          rw [if_pos hpar, if_pos hedge] at hp0
          have hbe := hp0.2.1
          have hb3 := hp0.2.2.1
          have hb4 := hp0.2.2.2
          have hstep : updateStep evm ss base i idx maxN cur = stepEdge evm ss base i idx cur := by
            unfold updateStep; rw [if_pos hpar, if_pos hedge]
          rw [hstep]
          rw [updateBody_edge hss h1 hi hidx hmax hcur hcont hpar hedge hbe hp0.1 hb3 hb4]
          refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
              lookup_ok_evm (e' := evm)]
          exact hss)
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
              lookup_ok_evm (e' := evm)]
          exact h1)
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
          have hstep : updateStep evm ss base i idx maxN cur
              = stepEven evm base i idx cur := by
            unfold updateStep; rw [if_pos hpar, if_neg hedge]
          rw [hstep]
          rw [updateBody_even hss h1 hi hidx hmax hcur hcont hpar hedge hp0.2.1
              hp0.2.2.1 hp0.2.2.2.1 hp0.1 hp0.2.2.2.2.1 hp0.2.2.2.2.2]
          refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
          exact hss)
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
          exact h1)
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
        have hstep : updateStep evm ss base i idx maxN cur
            = stepOdd evm base i idx cur := by
          unfold updateStep; rw [if_neg hpar]
        rw [hstep]
        rw [updateBody_odd hss h1 hi hidx hmax hcur hcont hpar hp0.2.1 hp0.2.2.1
          hp0.1 hp0.2.2.2.1 hp0.2.2.2.2]
        refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        exact hss)
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
        exact h1)
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
    obtain ⟨bs, hexec, hbss, hb1, hbi, hbidx, hbmax, hbcur⟩ := hbody
    rw [hexec]
    dsimp only
    rw [reviveJump_of_isOk
      (show isOk (Ok (updateStep evm ss base i idx maxN cur).2 bs) from trivial)]
    have hpost : exec (fb+1) (.Block L2InteropCommitmentTree.Common.for_4843491680166179088_post)
        (Ok (updateStep evm ss base i idx maxN cur).2 bs)
        = Ok (updateStep evm ss base i idx maxN cur).2 (bs.insert "var_i" (i + 1)) := by
      unfold _root_.L2InteropCommitmentTree.Common.for_4843491680166179088_post
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
    have hw1 : (updateWalk ss base 1 evm i idx maxN cur).1
        = (updateStep evm ss base i idx maxN cur).2 := by
      simp only [updateWalk]
    have hssStep : ((updateStep evm ss base i idx maxN cur).2).sload ss = evm.sload ss := by
      rw [← hw1]
      exact hssinv 1 (by omega)
    obtain ⟨σ', hσ'⟩ := ih (fuel := fb+1)
      (evm := (updateStep evm ss base i idx maxN cur).2)
      (σ := bs.insert "var_i" (i + 1))
      (ss := ss) (base := base) (i := i + 1) (idx := Fin.shiftRight idx 1)
      (maxN := Fin.shiftRight maxN 1) (cur := (updateStep evm ss base i idx maxN cur).1)
      (by rw [lookup_insert_ne_fin (by decide)]; exact hbss)
      (by rw [lookup_insert_ne_fin (by decide)]; exact hb1)
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
          have h2 : (updateWalk ss base (j+1) evm i idx maxN cur).1
              = (updateWalk ss base j (updateStep evm ss base i idx maxN cur).2 (i+1)
                  (Fin.shiftRight idx 1) (Fin.shiftRight maxN 1)
                  (updateStep evm ss base i idx maxN cur).1).1 := by
            simp only [updateWalk]
          rw [← h2, h1, hssStep])
      (by omega)
    have hwstep : updateWalk ss base (k+1) evm i idx maxN cur
        = updateWalk ss base k (updateStep evm ss base i idx maxN cur).2 (i+1)
            (Fin.shiftRight idx 1) (Fin.shiftRight maxN 1)
            (updateStep evm ss base i idx maxN cur).1 := by
      simp only [updateWalk]
    refine ⟨σ', ?_, ?_⟩
    · try simp only [overwrite?_of_Ok]
      rw [hwstep]
      exact hσ'.1
    · rw [hwstep]
      exact hσ'.2

/-! ## U4 — the `fun_updateLeaf` top-level closed form -/

/-- Closed form of the element-0 accessor `…_5278(array)` (nonempty array):
returns `(keccak(array), 0)`. -/
lemma storage_array_index0_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {arr : Literal}
    {sv ov : Identifier}
    (hne : evm.sload arr ≠ 0) :
    execCall (fuel+1) storage_array_index_access_bytes32_dyn__dyn_5278 [sv, ov]
        (Ok evm store, [arr])
      = Ok (arrOut evm arr).2
          (Finmap.insert sv (arrOut evm arr).1 (Finmap.insert ov 0 store)) := by
  unfold execCall call storage_array_index_access_bytes32_dyn__dyn_5278
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
  rw [primCall_keccakOut]
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

/-- The evm after the leaf write: two `arrOut` slot computations then the
`sstore` of the new leaf hash at element `idx` of the level-0 array. -/
def leafWriteEvm (σ : EVMState) (ss idx leaf : UInt256) : EVMState :=
  (arrOut (arrOut σ (ss + 2)).2 (arrOut σ (ss + 2)).1).2.sstore
    ((arrOut (arrOut σ (ss + 2)).2 (arrOut σ (ss + 2)).1).1 + idx) leaf

/-- The leaf-write block of `updateLeaf`. -/
private lemma leafWrite_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {ss idx leaf : Literal}
    (hss : (Ok evm σ)["var_self_slot"]!! = ss)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hleaf : (Ok evm σ)["var_itemHash"]!! = leaf)
    (hne : evm.sload (ss + 2) ≠ 0)
    (hb : idx < (arrOut evm (ss + 2)).2.sload (arrOut evm (ss + 2)).1) :
    exec (fuel+1) (.Block
        [LetPrimCall ["_1"] .Add [Var "var_self_slot", Lit 2],
         LetCall ["_2", "_3"] storage_array_index_access_bytes32_dyn__dyn_5278
           [Var "_1"],
         LetCall ["_4", "_5"] storage_array_index_access_bytes32_dyn__dyn
           [Var "_2", Var "var_index"],
         ExprStmtCall update_storage_value_bytes32_to_bytes32
           [Var "_4", Var "_5", Var "var_itemHash"],
         LetEq "var_currentHash" (Var "var_itemHash")]) (Ok evm σ)
      = Ok (leafWriteEvm evm ss idx leaf)
          (Finmap.insert "var_currentHash" leaf
            (Finmap.insert "_4"
                ((arrOut (arrOut evm (ss + 2)).2 (arrOut evm (ss + 2)).1).1 + idx)
              (Finmap.insert "_5" 0
                (Finmap.insert "_2" (arrOut evm (ss + 2)).1
                  (Finmap.insert "_3" 0
                    (Finmap.insert "_1" (ss + 2) σ)))))) := by
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  have hleafe : ∀ e : EVMState, (Ok e σ)["var_itemHash"]!! = leaf := fun _ => hleaf
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMAdd', multifill_cons, multifill_nil]
  rw [hss]
  simp only [insert_Ok]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [storage_array_index0_call hne]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hidxe]
  rw [storage_array_index_call hb]
  rw [cons, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hleafe]
  rw [update_storage_call_0]
  rw [cons, nil, LetEq']
  simp only [Var']
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hleafe]
  simp only [insert_Ok]
  rfl

/-- The counter block `{ let var_i := 0; var_i := 0 }`. -/
private lemma vari_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} :
    exec (fuel+1) (.Block [LetEq "var_i" (Lit 0), Assign "var_i" (Lit 0)]) (Ok evm σ)
      = Ok evm (Finmap.insert "var_i" 0 (Finmap.insert "var_i" 0 σ)) := by
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  rw [cons, nil, Assign']
  simp only [Lit', eval, insert_Ok]

/-- **U4 — CLOSED FORM OF `fun_updateLeaf`.**  Success path: the guard passes,
the new leaf hash is stored at position `idx` of level 0, the Merkle path is
recomputed level by level (`updateWalk`), and the new root is returned. -/
theorem updateLeaf_call
    {evm : EVMState} {store : VarStore} {fuel k : ℕ}
    {ss idx leaf : Literal} {v : Identifier}
    (hsub0 : evm.sload (ss + 1) ≠ 0)
    (hle : ¬ (idx > evm.sload (ss + 1) - 1))
    (hne2 : evm.sload (ss + 2) ≠ 0)
    (hbidx : idx < (arrOut evm (ss + 2)).2.sload (arrOut evm (ss + 2)).1)
    (hk : ((leafWriteEvm evm ss idx leaf).sload ss).val = k)
    (hpass : ∀ j, j < k → WalkOK ss (ss + 2)
        (updateWalk ss (ss + 2) j (leafWriteEvm evm ss idx leaf) 0 idx
          (evm.sload (ss + 1) - 1) leaf))
    (hssinv : ∀ j, j ≤ k →
        ((updateWalk ss (ss + 2) j (leafWriteEvm evm ss idx leaf) 0 idx
            (evm.sload (ss + 1) - 1) leaf).1).sload ss
          = (leafWriteEvm evm ss idx leaf).sload ss)
    (hfuel : 2 * k + 2 ≤ fuel) :
    execCall (fuel+1) fun_updateLeaf [v] (Ok evm store, [ss, idx, leaf])
      = Ok (updateWalk ss (ss + 2) k (leafWriteEvm evm ss idx leaf) 0 idx
            (evm.sload (ss + 1) - 1) leaf).1
          (store.insert v
            (updateWalk ss (ss + 2) k (leafWriteEvm evm ss idx leaf) 0 idx
              (evm.sload (ss + 1) - 1) leaf).2.2.2.2) := by
  unfold execCall call fun_updateLeaf
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  -- normalize the regenerated accessor names to the __dyn variants this
  -- proof was written against (the definitions are rfl-equal)
  simp only [show storage_array_index_access_bytes32_dyn_ptr_5303
      = storage_array_index_access_bytes32_dyn__dyn_5278 from rfl,
    show storage_array_index_access_bytes32_dyn_ptr
      = storage_array_index_access_bytes32_dyn__dyn from rfl]
  set s0 := (Ok evm store)☎️⟦["var_self_slot", "var_index", "var_itemHash"],
      [ss, idx, leaf]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["var_self_slot"]!! = ss := by rw [hs0]; exact lookup_initcall_1
  have hp2 : s0["var_index"]!! = idx := by rw [hs0]; exact lookup_initcall_2 (by decide)
  have hp3 : s0["var_itemHash"]!! = leaf := by
    rw [hs0]; exact lookup_initcall_3 (by decide) (by decide)
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq] at hp1 hp2 hp3 ⊢
  have hp1e : ∀ e : EVMState, (Ok e σ0)["var_self_slot"]!! = ss := fun _ => hp1
  have hp2e : ∀ e : EVMState, (Ok e σ0)["var_index"]!! = idx := fun _ => hp2
  have hp3e : ∀ e : EVMState, (Ok e σ0)["var_itemHash"]!! = leaf := fun _ => hp3
  -- statement 1: split_expr_0 := add(var_self_slot, 1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMAdd', multifill_cons, multifill_nil]
  rw [hp1]
  simp only [insert_Ok]
  -- statement 2: split_expr_1 := sload(split_expr_0)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  -- statement 3: var_maxNodeNumber := checked_sub(split_expr_1)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [checked_sub_call hsub0]
  -- statement 4: the range guard is skipped
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMGt']
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hp2]
  rw [lookup_insert_self_fin]
  rw [show fromBool (idx > evm.sload (ss + 1) - 1) = (0 : UInt256) from by
    rw [decide_eq_false hle]; rfl]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- statement 5: the leaf write
  rw [cons]
  rw [leafWrite_block (ss := ss) (idx := idx) (leaf := leaf)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hp1)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hp2)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hp3)
    hne2 hbidx]
  -- statement 6: the counter block
  rw [cons]
  rw [vari_block]
  -- statement 7: the For loop — fold the inline AST to the named defs
  rw [cons]
  rw [show ([AssignPrimCall ["var_i"] .Add [Var "var_i", Lit 1]] : List Stmt)
        = _root_.L2InteropCommitmentTree.Common.for_4843491680166179088_post from rfl,
      show ([LetPrimCall ["split_expr_4"] .Sload [Var "var_self_slot"],
             LetPrimCall ["split_expr_5"] .Lt [Var "var_i", Var "split_expr_4"],
             If (PrimCall .Iszero [Var "split_expr_5"]) [Stmt.Break],
             LetCall ["split_expr_6"] mod_uint256 [Var "var_index"],
             Switch (PrimCall .Iszero [Var "split_expr_6"])
               [(0, [.Block
                      [LetCall ["_6", "_7"] storage_array_index_access_bytes32_dyn__dyn
                         [Var "_1", Var "var_i"],
                       LetCall ["split_expr_7"] checked_sub_uint256 [Var "var_index"],
                       LetCall ["_8", "_9"] storage_array_index_access_bytes32_dyn__dyn
                         [Var "_6", Var "split_expr_7"],
                       LetPrimCall ["split_expr_8"] .Sload [Var "_8"],
                       LetCall ["split_expr_9"] extract_from_storage_value_dynamict_bytes32
                         [Var "split_expr_8", Var "_9"]],
                     .Block
                      [AssignCall ["var_currentHash"] fun_efficientHash
                         [Var "split_expr_9", Var "var_currentHash"]]])]
               [LetEq "expr" (Lit 0),
                Switch (PrimCall .Eq [Var "var_maxNodeNumber", Var "var_index"])
                  [(0, [LetCall ["_10", "_11"] storage_array_index_access_bytes32_dyn__dyn
                          [Var "_1", Var "var_i"],
                        LetCall ["split_expr_10"] checked_add_uint256 [Var "var_index"],
                        LetCall ["_12", "_13"] storage_array_index_access_bytes32_dyn__dyn
                          [Var "_10", Var "split_expr_10"],
                        LetPrimCall ["split_expr_11"] .Sload [Var "_12"],
                        AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
                          [Var "split_expr_11", Var "_13"]])]
                  [LetPrimCall ["split_expr_12"] .Add [Var "var_self_slot", Lit 3],
                   LetCall ["_14", "_15"] storage_array_index_access_bytes32_dyn__dyn
                     [Var "split_expr_12", Var "var_i"],
                   LetPrimCall ["split_expr_13"] .Sload [Var "_14"],
                   AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
                     [Var "split_expr_13", Var "_15"]],
                AssignCall ["var_currentHash"] fun_efficientHash
                  [Var "var_currentHash", Var "expr"]],
             .Block
              [AssignCall ["var_index"] checked_div_uint256 [Var "var_index"],
               AssignCall ["var_maxNodeNumber"] checked_div_uint256 [Var "var_maxNodeNumber"],
               LetCall ["split_expr_14"] checked_add_uint256 [Var "var_i"],
               LetCall ["_16", "_17"] storage_array_index_access_bytes32_dyn__dyn
                 [Var "_1", Var "split_expr_14"],
               LetCall ["_18", "_19"] storage_array_index_access_bytes32_dyn__dyn
                 [Var "_16", Var "var_index"]],
             .Block
              [ExprStmtCall update_storage_value_bytes32_to_bytes32
                 [Var "_18", Var "_19", Var "var_currentHash"]]] : List Stmt)
        = _root_.L2InteropCommitmentTree.Common.for_4843491680166179088_body from rfl,
      show (Lit 1 : Expr)
        = _root_.L2InteropCommitmentTree.Common.for_4843491680166179088_cond from rfl]
  obtain ⟨σ', hσ'eq, hσ'cur⟩ := update_loop k (fuel := fuel+1)
    (evm := leafWriteEvm evm ss idx leaf)
    (σ := Finmap.insert "var_i" 0 (Finmap.insert "var_i" 0
      (Finmap.insert "var_currentHash" leaf
        (Finmap.insert "_4"
            ((arrOut (arrOut evm (ss + 2)).2 (arrOut evm (ss + 2)).1).1 + idx)
          (Finmap.insert "_5" 0
            (Finmap.insert "_2" (arrOut evm (ss + 2)).1
              (Finmap.insert "_3" 0
                (Finmap.insert "_1" (ss + 2)
                  (Finmap.insert "var_maxNodeNumber" (evm.sload (ss + 1) - 1)
                    (Finmap.insert "split_expr_1" (evm.sload (ss + 1))
                      (Finmap.insert "split_expr_0" (ss + 1) σ0)))))))))))
    (ss := ss) (base := ss + 2) (i := 0) (idx := idx)
    (maxN := evm.sload (ss + 1) - 1) (cur := leaf)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hp1e _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_self_fin])
    (by exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hp2e _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_self_fin])
    (by rw [show ((0 : UInt256)).val = 0 from by decide]; omega)
    hpass hssinv (by omega)
  rw [hσ'eq]
  -- statement 8: var := var_currentHash
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

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
