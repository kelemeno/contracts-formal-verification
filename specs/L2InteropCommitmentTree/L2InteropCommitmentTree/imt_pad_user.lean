import Clear.ReasoningPrinciple

import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_push_user
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_5765234204941653661

/-
  P4a — the `fun_pushNewLeaf` padding loop, body layer.

  For a non-first leaf, `pushNewLeaf` extends the frontier: at each level where
  the old and new max node numbers differ, it pushes the side-array node (the
  edge duplicate) onto the level array (`padStep`), halving both counters.
  The loop exits by level count or by counter agreement (two break paths).

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

private lemma insert_Ok {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

private lemma evm_Ok {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok]; exact lookup_insert_of_ne h

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

/-- One padding step at level `i`: read the side node, push it onto the
level-`i` array. -/
def padStep (σ : EVMState) (i : UInt256) : EVMState :=
  pushEvm (arrOut (arrOut σ 2).2 3).2 ((arrOut σ 2).1 + i)
    ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut (arrOut σ 2).2 3).1 + i))

/-- The side-node push block of the padding loop. -/
private lemma pushSide_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {i : Literal}
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hb1 : i < evm.sload 2)
    (hb2 : i < (arrOut evm 2).2.sload 3)
    (hlen : (((arrOut (arrOut evm 2).2 3).2).sload ((arrOut evm 2).1 + i)).val
      < 18446744073709551616)
    (haccB : ((arrOut (arrOut evm 2).2 3).2.lookupAccount
        (arrOut (arrOut evm 2).2 3).2.execution_env.code_owner).isSome) :
    exec (fuel+1) (.Block
        [LetCall ["_7", "_8"] storage_array_index_access_bytes32_dyn__dyn
           [Lit 2, Var "var_i"],
         LetCall ["_9", "_10"] storage_array_index_access_bytes32_dyn__dyn
           [Lit 3, Var "var_i"],
         LetPrimCall ["split_expr_7"] .Sload [Var "_9"],
         LetCall ["split_expr_8"] extract_from_storage_value_dynamict_bytes32
           [Var "split_expr_7", Var "_10"],
         ExprStmtCall array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
           [Var "_7", Var "split_expr_8"]]) (Ok evm σ)
      = Ok (padStep evm i)
          (Finmap.insert "split_expr_8"
              ((arrOut (arrOut evm 2).2 3).2.sload ((arrOut (arrOut evm 2).2 3).1 + i))
            (Finmap.insert "split_expr_7"
                ((arrOut (arrOut evm 2).2 3).2.sload ((arrOut (arrOut evm 2).2 3).1 + i))
              (Finmap.insert "_9" ((arrOut (arrOut evm 2).2 3).1 + i)
                (Finmap.insert "_10" 0
                  (Finmap.insert "_7" ((arrOut evm 2).1 + i)
                    (Finmap.insert "_8" 0 σ)))))) := by
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [hi]
  rw [storage_array_index_call hb1]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hie]
  rw [storage_array_index_call hb2]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [evm_Ok, insert_Ok]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [extract_call_0]
  rw [cons, nil, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [lookup_insert_self_fin]
  rw [array_push_call hlen haccB]
  rfl

/-- The counter-halving block of the padding loop. -/
private lemma divPair_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {om m : Literal}
    (hom : (Ok evm σ)["var_oldMaxNodeNumber"]!! = om)
    (hm : (Ok evm σ)["var_maxNodeNumber"]!! = m) :
    exec (fuel+1) (.Block
        [AssignCall ["var_maxNodeNumber"] checked_div_uint256 [Var "var_maxNodeNumber"],
         AssignCall ["var_oldMaxNodeNumber"] checked_div_uint256 [Var "var_oldMaxNodeNumber"]])
        (Ok evm σ)
      = Ok evm (Finmap.insert "var_oldMaxNodeNumber" (Fin.shiftRight om 1)
          (Finmap.insert "var_maxNodeNumber" (Fin.shiftRight m 1) σ)) := by
  have home : ∀ e : EVMState, (Ok e σ)["var_oldMaxNodeNumber"]!! = om := fun _ => hom
  rw [cons, AssignCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [hm, div2_call]
  simp only [insert_Ok]
  rw [cons, nil, AssignCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), home, div2_call]
  simp only [insert_Ok]

private lemma exec_checkpoint {c : Jump} {fuel : ℕ} {stmt : Stmt} :
    exec fuel stmt (Checkpoint c) = Checkpoint c := by
  have h := Clear.JumpLemmas.exec_Jump (c := c) (s := Checkpoint c) (fuel := fuel) (stmt := stmt) rfl
  rcases hres : exec fuel stmt (Checkpoint c) with _ | _ | c'
  · rw [hres] at h; exact absurd h (by unfold isJump; simp)
  · rw [hres] at h; exact absurd h (by unfold isJump; simp)
  · rw [hres] at h
    have : c = c' := h
    rw [this]

private lemma break_block {fuel : ℕ} {evm : EVMState} {σ : VarStore} :
    exec (fuel+1) (.Block [Stmt.Break]) (Ok evm σ) = Checkpoint (.Break evm σ) := by
  rw [cons, nil, Break']
  rfl

/-- **One continue pass** of the padding loop equals `padStep` (both guards
pass: below the level count, counters still differ). -/
lemma padBody
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {i om m : Literal}
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hom : (Ok evm σ)["var_oldMaxNodeNumber"]!! = om)
    (hm : (Ok evm σ)["var_maxNodeNumber"]!! = m)
    (hbreak : i < evm.sload 0)
    (hne : om ≠ m)
    (hb1 : i < evm.sload 2)
    (hb2 : i < (arrOut evm 2).2.sload 3)
    (hlen : (((arrOut (arrOut evm 2).2 3).2).sload ((arrOut evm 2).1 + i)).val
      < 18446744073709551616)
    (haccB : ((arrOut (arrOut evm 2).2 3).2.lookupAccount
        (arrOut (arrOut evm 2).2 3).2.execution_env.code_owner).isSome) :
    exec (fuel+1) (.Block L2InteropCommitmentTree.Common.for_5765234204941653661_body)
        (Ok evm σ)
      = Ok (padStep evm i)
          (Finmap.insert "var_oldMaxNodeNumber" (Fin.shiftRight om 1)
            (Finmap.insert "var_maxNodeNumber" (Fin.shiftRight m 1)
              (Finmap.insert "split_expr_8"
                  ((arrOut (arrOut evm 2).2 3).2.sload ((arrOut (arrOut evm 2).2 3).1 + i))
                (Finmap.insert "split_expr_7"
                    ((arrOut (arrOut evm 2).2 3).2.sload ((arrOut (arrOut evm 2).2 3).1 + i))
                  (Finmap.insert "_9" ((arrOut (arrOut evm 2).2 3).1 + i)
                    (Finmap.insert "_10" 0
                      (Finmap.insert "_7" ((arrOut evm 2).1 + i)
                        (Finmap.insert "_8" 0
                          (Finmap.insert "split_expr_6" 1
                            (Finmap.insert "split_expr_5" (evm.sload 0) σ)))))))))) := by
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  have home : ∀ e : EVMState, (Ok e σ)["var_oldMaxNodeNumber"]!! = om := fun _ => hom
  have hme : ∀ e : EVMState, (Ok e σ)["var_maxNodeNumber"]!! = m := fun _ => hm
  unfold _root_.L2InteropCommitmentTree.Common.for_5765234204941653661_body
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  simp only [evm_Ok, insert_Ok]
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
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMEq']
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), home]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hme]
  rw [show fromBool (om = m) = (0 : UInt256) from by rw [decide_eq_false hne]; rfl]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  rw [cons]
  rw [pushSide_block (i := i)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact hie _)
    hb1 hb2 hlen haccB]
  rw [cons, nil]
  rw [divPair_block (om := om) (m := m)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact home _)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact hme _)]
  try rfl

/-- **Exit by level count**: the first guard breaks. -/
lemma padBody_break1
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {i : Literal}
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hstop : ¬ (i < evm.sload 0)) :
    exec (fuel+1) (.Block L2InteropCommitmentTree.Common.for_5765234204941653661_body)
        (Ok evm σ)
      = Checkpoint (.Break evm
          (Finmap.insert "split_expr_6" 0
            (Finmap.insert "split_expr_5" (evm.sload 0) σ))) := by
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  unfold _root_.L2InteropCommitmentTree.Common.for_5765234204941653661_body
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  simp only [evm_Ok, insert_Ok]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hie, lookup_insert_self_fin]
  rw [show fromBool (i < evm.sload 0) = (0 : UInt256) from by
    rw [decide_eq_false hstop]; rfl]
  simp only [insert_Ok]
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [head', List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  rw [break_block]
  rw [cons, exec_checkpoint, cons, exec_checkpoint, cons, nil, exec_checkpoint]

/-- **Exit by counter agreement**: the second guard breaks. -/
lemma padBody_break2
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {i om m : Literal}
    (hi : (Ok evm σ)["var_i"]!! = i)
    (hom : (Ok evm σ)["var_oldMaxNodeNumber"]!! = om)
    (hm : (Ok evm σ)["var_maxNodeNumber"]!! = m)
    (hcont : i < evm.sload 0)
    (heq : om = m) :
    exec (fuel+1) (.Block L2InteropCommitmentTree.Common.for_5765234204941653661_body)
        (Ok evm σ)
      = Checkpoint (.Break evm
          (Finmap.insert "split_expr_6" 1
            (Finmap.insert "split_expr_5" (evm.sload 0) σ))) := by
  have hie : ∀ e : EVMState, (Ok e σ)["var_i"]!! = i := fun _ => hi
  have home : ∀ e : EVMState, (Ok e σ)["var_oldMaxNodeNumber"]!! = om := fun _ => hom
  have hme : ∀ e : EVMState, (Ok e σ)["var_maxNodeNumber"]!! = m := fun _ => hm
  unfold _root_.L2InteropCommitmentTree.Common.for_5765234204941653661_body
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  simp only [evm_Ok, insert_Ok]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hie, lookup_insert_self_fin]
  rw [show fromBool (i < evm.sload 0) = (1 : UInt256) from by
    rw [decide_eq_true hcont]; rfl]
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
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMEq']
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), home]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hme]
  rw [show fromBool (om = m) = (1 : UInt256) from by rw [decide_eq_true heq]; rfl]
  try simp only [head', List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  rw [break_block]
  rw [cons, exec_checkpoint, cons, nil, exec_checkpoint]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
