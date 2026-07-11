import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_4843491680166179088
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_storage_atoms_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_hash_user

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

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
