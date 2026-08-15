import Clear.ReasoningPrinciple
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn

import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_push_user
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_5765234204941653661
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_1084122831851539501
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_3948411532618903895
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_hash_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_update_fold_user
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_pushNewLeaf

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
private lemma ptr_norm₁ : storage_array_index_access_bytes32_dyn_ptr
    = storage_array_index_access_bytes32_dyn__dyn := rfl

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

private lemma lookup_ok_evm {e e' : EVMState} {σ : VarStore} {k : Identifier} :
    (Ok e σ)[k]!! = (Ok e' σ)[k]!! := rfl

private lemma reviveJump_Ok {e : EVMState} {σ : VarStore} : 🧟 (Ok e σ) = Ok e σ := rfl

/-- The padding walk state after `j` levels: `(evm, i, oldMax, max)`. -/
def padWalk : ℕ → EVMState → UInt256 → UInt256 → UInt256
    → EVMState × UInt256 × UInt256 × UInt256
  | 0, σ, i, om, m => (σ, i, om, m)
  | (j+1), σ, i, om, m =>
      padWalk j (padStep σ i) (i + 1) (Fin.shiftRight om 1) (Fin.shiftRight m 1)

/-- Per-pass side conditions of the padding loop. -/
def PadOK (t : EVMState × UInt256 × UInt256 × UInt256) : Prop :=
  t.2.1.val + 1 < 2 ^ 256 ∧
  t.2.1 < t.1.sload 2 ∧
  t.2.1 < (arrOut t.1 2).2.sload 3 ∧
  (((arrOut (arrOut t.1 2).2 3).2).sload ((arrOut t.1 2).1 + t.2.1)).val
    < 18446744073709551616 ∧
  ((arrOut (arrOut t.1 2).2 3).2.lookupAccount
      (arrOut (arrOut t.1 2).2 3).2.execution_env.code_owner).isSome

/-- The variables the padding loop writes. -/
def padVars : List Identifier :=
  ["var_i", "var_oldMaxNodeNumber", "var_maxNodeNumber", "split_expr_5",
   "split_expr_6", "_7", "_8", "_9", "_10", "split_expr_7", "split_expr_8"]

/-- **P4c — THE PADDING LOOP IS `padWalk`.**  Under per-pass bounds, `k`
continue passes then a break (by level count or counter agreement); every
variable outside `padVars` is preserved. -/
lemma pad_loop :
    ∀ (k : ℕ) {fuel : ℕ} {evm : EVMState} {σ : VarStore} {i om m : Literal},
    (Ok evm σ)["var_i"]!! = i →
    (Ok evm σ)["var_oldMaxNodeNumber"]!! = om →
    (Ok evm σ)["var_maxNodeNumber"]!! = m →
    (∀ j, j < k → (padWalk j evm i om m).2.1 < (padWalk j evm i om m).1.sload 0
      ∧ (padWalk j evm i om m).2.2.1 ≠ (padWalk j evm i om m).2.2.2) →
    (¬ ((padWalk k evm i om m).2.1 < (padWalk k evm i om m).1.sload 0)
      ∨ (padWalk k evm i om m).2.2.1 = (padWalk k evm i om m).2.2.2) →
    (∀ j, j < k → PadOK (padWalk j evm i om m)) →
    2 * k + 3 ≤ fuel →
    ∃ σ' : VarStore,
      exec fuel (.For L2InteropCommitmentTree.Common.for_5765234204941653661_cond
          L2InteropCommitmentTree.Common.for_5765234204941653661_post
          L2InteropCommitmentTree.Common.for_5765234204941653661_body) (Ok evm σ)
        = Ok (padWalk k evm i om m).1 σ'
      ∧ ∀ key : Identifier, key ∉ padVars →
          (Ok (padWalk k evm i om m).1 σ')[key]!! = (Ok evm σ)[key]!! := by
  intro k
  induction k with
  | zero =>
    intro fuel evm σ i om m hi hom hm _ hstop _ hfuel
    rcases fuel with _ | _ | f
    · omega
    · omega
    rw [For']
    dsimp only
    unfold _root_.L2InteropCommitmentTree.Common.for_5765234204941653661_cond
    simp only [eval, Lit', mkOk_of_isOk (show isOk (Ok evm σ) from trivial)]
    rw [if_neg (by decide : ¬ ((1 : UInt256) = 0))]
    obtain ⟨fb, rfl⟩ : ∃ fb, f = fb + 1 := ⟨f - 1, by omega⟩
    simp only [padWalk] at hstop
    rcases hstop with hstop | heqc
    · -- exit by level count
      rw [padBody_break1 hi hstop]
      dsimp only
      refine ⟨Finmap.insert "split_expr_6" 0
        (Finmap.insert "split_expr_5" (evm.sload 0) σ), ?_, ?_⟩
      · rw [show (🧟 (Checkpoint (.Break evm (Finmap.insert "split_expr_6" 0
            (Finmap.insert "split_expr_5" (evm.sload 0) σ)))) : State)
          = Ok evm (Finmap.insert "split_expr_6" 0
              (Finmap.insert "split_expr_5" (evm.sload 0) σ)) from rfl]
        simp only [overwrite?_of_Ok]
        rfl
      · intro key hkey
        rw [lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
            lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide))]
        simp only [padWalk]
    · -- exit by counter agreement
      by_cases hc : i < evm.sload 0
      · rw [padBody_break2 hi hom hm hc heqc]
        dsimp only
        refine ⟨Finmap.insert "split_expr_6" 1
          (Finmap.insert "split_expr_5" (evm.sload 0) σ), ?_, ?_⟩
        · rw [show (🧟 (Checkpoint (.Break evm (Finmap.insert "split_expr_6" 1
              (Finmap.insert "split_expr_5" (evm.sload 0) σ)))) : State)
            = Ok evm (Finmap.insert "split_expr_6" 1
                (Finmap.insert "split_expr_5" (evm.sload 0) σ)) from rfl]
          simp only [overwrite?_of_Ok]
          rfl
        · intro key hkey
          rw [lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
              lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide))]
          simp only [padWalk]
      · rw [padBody_break1 hi hc]
        dsimp only
        refine ⟨Finmap.insert "split_expr_6" 0
          (Finmap.insert "split_expr_5" (evm.sload 0) σ), ?_, ?_⟩
        · rw [show (🧟 (Checkpoint (.Break evm (Finmap.insert "split_expr_6" 0
              (Finmap.insert "split_expr_5" (evm.sload 0) σ)))) : State)
            = Ok evm (Finmap.insert "split_expr_6" 0
                (Finmap.insert "split_expr_5" (evm.sload 0) σ)) from rfl]
          simp only [overwrite?_of_Ok]
          rfl
        · intro key hkey
          rw [lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
              lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide))]
          simp only [padWalk]
  | succ k ih =>
    intro fuel evm σ i om m hi hom hm hcont hstop hpass hfuel
    obtain ⟨fb, rfl⟩ : ∃ fb, fuel = fb + 1 + 1 + 1 := ⟨fuel - 3, by omega⟩
    have h0 := hcont 0 (by omega)
    simp only [padWalk] at h0
    have hp0 := hpass 0 (by omega)
    simp only [padWalk, PadOK] at hp0
    rw [For']
    dsimp only
    unfold _root_.L2InteropCommitmentTree.Common.for_5765234204941653661_cond
    simp only [eval, Lit', mkOk_of_isOk (show isOk (Ok evm σ) from trivial)]
    rw [if_neg (by decide : ¬ ((1 : UInt256) = 0))]
    rw [padBody hi hom hm h0.1 h0.2 hp0.2.1 hp0.2.2.1 hp0.2.2.2.1 hp0.2.2.2.2]
    dsimp only
    rw [show (🧟 (Ok (padStep evm i)
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
                          (Finmap.insert "split_expr_5" (evm.sload 0) σ))))))))))) : State)
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
                            (Finmap.insert "split_expr_5" (evm.sload 0) σ)))))))))) from rfl]
    -- the post bumps var_i
    rw [show exec (fb+1) (.Block L2InteropCommitmentTree.Common.for_5765234204941653661_post)
        (Ok (padStep evm i)
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
                            (Finmap.insert "split_expr_5" (evm.sload 0) σ)))))))))))
        = Ok (padStep evm i)
            (Finmap.insert "var_i" (i + 1)
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
                                (Finmap.insert "split_expr_5" (evm.sload 0) σ))))))))))) from by
      unfold _root_.L2InteropCommitmentTree.Common.for_5765234204941653661_post
      simp only [cons, nil, AssignPrimCall', evalArgs, evalTail, cons', head',
                 reverse', multifill', PrimCall', Lit', Var', execPrimCall,
                 evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
                 List.singleton_append, EVMAdd', multifill_cons, multifill_nil]
      rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
          lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
          lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
          lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
          lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
      rw [lookup_ok_evm (e' := evm), hi]
      rfl]
    try simp only [overwrite?_of_Ok]
    obtain ⟨σ', hσ'eq, hσ'pres⟩ := ih (fuel := fb+1)
      (evm := padStep evm i)
      (σ := Finmap.insert "var_i" (i + 1)
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
                          (Finmap.insert "split_expr_5" (evm.sload 0) σ)))))))))))
      (i := i + 1) (om := Fin.shiftRight om 1) (m := Fin.shiftRight m 1)
      (by exact lookup_insert_self_fin)
      (by rw [lookup_insert_ne_fin (by decide)]; exact lookup_insert_self_fin)
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact lookup_insert_self_fin)
      (by intro j hj
          have := hcont (j+1) (by omega)
          simpa only [padWalk] using this)
      (by have := hstop
          simpa only [padWalk] using this)
      (by intro j hj
          have := hpass (j+1) (by omega)
          simpa only [padWalk] using this)
      (by omega)
    refine ⟨σ', ?_, ?_⟩
    · try simp only [overwrite?_of_Ok]
      rw [show padWalk (k+1) evm i om m
          = padWalk k (padStep evm i) (i+1) (Fin.shiftRight om 1) (Fin.shiftRight m 1)
        from by simp only [padWalk]]
      exact hσ'eq
    · intro key hkey
      rw [show padWalk (k+1) evm i om m
          = padWalk k (padStep evm i) (i+1) (Fin.shiftRight om 1) (Fin.shiftRight m 1)
        from by simp only [padWalk]]
      rw [hσ'pres key hkey]
      rw [lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
          lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
          lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
          lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
          lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
          lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
          lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
          lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
          lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
          lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
          lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide))]
      exact lookup_ok_evm

/-! ## P5 — the growth branch -/

/-- Growth chunk A: bump the depth, locate the top side node. -/
private lemma growA_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {d : Literal}
    (h2 : (Ok evm σ)["_2"]!! = d)
    (hd1 : d + 1 ≠ 0)
    (hb3 : (d + 1) - 1 < (evm.sstore 0 (d + 1)).sload 3) :
    exec (fuel+1) (.Block
        [LetCall ["expr"] fun_uncheckedInc [Var "_2"],
         ExprStmtPrimCall .Sstore [Lit 0, Var "expr"],
         LetCall ["split_expr_2"] checked_sub_uint256 [Var "expr"],
         LetCall ["_3", "_4"] storage_array_index_access_bytes32_dyn__dyn
           [Lit 3, Var "split_expr_2"],
         LetPrimCall ["split_expr_3"] .Sload [Var "_3"]]) (Ok evm σ)
      = Ok (arrOut (evm.sstore 0 (d + 1)) 3).2
          (Finmap.insert "split_expr_3"
              ((arrOut (evm.sstore 0 (d + 1)) 3).2.sload
                ((arrOut (evm.sstore 0 (d + 1)) 3).1 + ((d + 1) - 1)))
            (Finmap.insert "_3"
                ((arrOut (evm.sstore 0 (d + 1)) 3).1 + ((d + 1) - 1))
              (Finmap.insert "_4" 0
                (Finmap.insert "split_expr_2" ((d + 1) - 1)
                  (Finmap.insert "expr" (d + 1) σ))))) := by
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [h2, uncheckedInc_call]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSstore', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [evm_Ok]
  rw [show ∀ (e : EVMState) (σ' : VarStore) (e' : EVMState),
      ((Ok e σ' : State).setEvm e') = Ok e' σ' from fun _ _ _ => rfl]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [checked_sub_call hd1]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [storage_array_index_call hb3]
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [evm_Ok, insert_Ok]

/-- Growth chunk B: hash the top side node with itself, push it. -/
private lemma growB_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {sv : Literal}
    (h3 : (Ok evm σ)["split_expr_3"]!! = sv)
    (h4 : (Ok evm σ)["_4"]!! = 0)
    (hlen3 : (((accOut evm sv sv).2).sload 3).val < 18446744073709551616)
    (hacc3 : ((accOut evm sv sv).2.lookupAccount
        (accOut evm sv sv).2.execution_env.code_owner).isSome) :
    exec (fuel+1) (.Block
        [LetCall ["_5"] extract_from_storage_value_dynamict_bytes32
           [Var "split_expr_3", Var "_4"],
         LetCall ["expr_1"] fun_efficientHash [Var "_5", Var "_5"],
         ExprStmtCall array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
           [Lit 3, Var "expr_1"],
         LetEq "size" (Lit 0),
         LetEq "_6" (Lit 0)]) (Ok evm σ)
      = Ok (pushEvm (accOut evm sv sv).2 3 (accOut evm sv sv).1)
          (Finmap.insert "_6" 0
            (Finmap.insert "size" 0
              (Finmap.insert "expr_1" (accOut evm sv sv).1
                (Finmap.insert "_5" sv σ)))) := by
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [h3, h4]
  rw [extract_call_0]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [efficientHash_call_acc]
  rw [cons, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [array_push_call hlen3 hacc3]
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  rw [cons, nil, LetEq']
  simp only [Lit', insert_Ok]

/-- Growth chunk C: allocate the 1-element buffer, store the hash, push the
new level array. -/
private lemma growC_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {h : Literal}
    (hh : (Ok evm σ)["expr_1"]!! = h)
    (hfp : (evm.mload 64).val + 32 ≤ 18446744073709551615)
    (hlen2 : (((evm.mstore 64 (evm.mload 64 + 32)).mstore (evm.mload 64) h).sload 2).val
      < 18446744073709551616)
    (hacc2 : (((evm.mstore 64 (evm.mload 64 + 32)).mstore (evm.mload 64) h).lookupAccount
        ((evm.mstore 64 (evm.mload 64 + 32)).mstore (evm.mload 64) h).execution_env.code_owner).isSome)
    (hstale : ¬ ((1 : UInt256)
      < (arrOut (((evm.mstore 64 (evm.mload 64 + 32)).mstore (evm.mload 64) h).sstore 2
            (((evm.mstore 64 (evm.mload 64 + 32)).mstore (evm.mload 64) h).sload 2 + 1)) 2).2.sload
          ((arrOut (((evm.mstore 64 (evm.mload 64 + 32)).mstore (evm.mload 64) h).sstore 2
              (((evm.mstore 64 (evm.mload 64 + 32)).mstore (evm.mload 64) h).sload 2 + 1)) 2).1
            + ((evm.mstore 64 (evm.mload 64 + 32)).mstore (evm.mload 64) h).sload 2)))
    (hfuel : 5 ≤ fuel) :
    exec (fuel+1) (.Block
        [Assign "_6" (Lit 0),
         Assign "size" (Lit 32),
         LetCall ["expr_mpos"] allocate_memory [Lit 32],
         ExprStmtPrimCall .Mstore [Var "expr_mpos", Var "expr_1"],
         ExprStmtCall array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr
           [Lit 2, Var "expr_mpos"]]) (Ok evm σ)
      = Ok (pushArrEvm ((evm.mstore 64 (evm.mload 64 + 32)).mstore (evm.mload 64) h)
            2 (evm.mload 64))
          (Finmap.insert "expr_mpos" (evm.mload 64)
            (Finmap.insert "size" 32
              (Finmap.insert "_6" 0 σ))) := by
  have hhe : ∀ e : EVMState, (Ok e σ)["expr_1"]!! = h := fun _ => hh
  rw [cons, Assign']
  simp only [Lit', eval, insert_Ok]
  rw [cons, Assign']
  simp only [Lit', eval, insert_Ok]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [allocate_memory_32_call hfp]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMMstore', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hhe]
  simp only [evm_Ok]
  rw [show ∀ (e : EVMState) (σ' : VarStore) (e' : EVMState),
      ((Ok e σ' : State).setEvm e') = Ok e' σ' from fun _ _ _ => rfl]
  rw [cons, nil, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [array_push_array_call hlen2 hacc2 hstale hfuel]
  try rfl

/-- **The taken padding-if**: initialize the counters and run the padding
loop (`pad_loop`).  Preserves every variable outside `padVars`. -/
lemma pad_if
    {evm : EVMState} {σ : VarStore} {fuel k : ℕ} {c : Literal}
    (h1 : (Ok evm σ)["_1"]!! = c)
    (hsp : (Ok evm σ)["split_expr_4"]!! = 0)
    (hc0 : c ≠ 0)
    (hcont : ∀ j, j < k → (padWalk j evm 0 (c - 1) c).2.1 < (padWalk j evm 0 (c - 1) c).1.sload 0
      ∧ (padWalk j evm 0 (c - 1) c).2.2.1 ≠ (padWalk j evm 0 (c - 1) c).2.2.2)
    (hstop : ¬ ((padWalk k evm 0 (c - 1) c).2.1 < (padWalk k evm 0 (c - 1) c).1.sload 0)
      ∨ (padWalk k evm 0 (c - 1) c).2.2.1 = (padWalk k evm 0 (c - 1) c).2.2.2)
    (hpass : ∀ j, j < k → PadOK (padWalk j evm 0 (c - 1) c))
    (hfuel : 2 * k + 2 ≤ fuel) :
    ∃ σ' : VarStore,
      exec (fuel+1) L2InteropCommitmentTree.Common.if_3948411532618903895 (Ok evm σ)
        = Ok (padWalk k evm 0 (c - 1) c).1 σ'
      ∧ ∀ key : Identifier, key ∉ padVars →
          (Ok (padWalk k evm 0 (c - 1) c).1 σ')[key]!! = (Ok evm σ)[key]!! := by
  have h1e : ∀ e : EVMState, (Ok e σ)["_1"]!! = c := fun _ => h1
  unfold _root_.L2InteropCommitmentTree.Common.if_3948411532618903895
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [hsp]
  rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [head', List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- prep: var_oldMaxNodeNumber := checked_sub(_1); var_maxNodeNumber := _1; var_i := 0; var_i := 0
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [h1, checked_sub_call hc0]
  rw [cons, LetEq']
  simp only [Var']
  rw [lookup_insert_ne_fin (by decide), h1e]
  simp only [insert_Ok]
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  rw [cons, Assign']
  simp only [Lit', eval, insert_Ok]
  -- the padding loop, folded to the named components
  rw [cons, nil]
  rw [show ([AssignPrimCall ["var_i"] .Add [Var "var_i", Lit 1]] : List Stmt)
        = _root_.L2InteropCommitmentTree.Common.for_5765234204941653661_post from rfl,
      show ([LetPrimCall ["split_expr_5"] .Sload [Lit 0],
             LetPrimCall ["split_expr_6"] .Lt [Var "var_i", Var "split_expr_5"],
             If (PrimCall .Iszero [Var "split_expr_6"]) [Stmt.Break],
             If (PrimCall .Eq [Var "var_oldMaxNodeNumber", Var "var_maxNodeNumber"]) [Stmt.Break],
             .Block
              [LetCall ["_7", "_8"] storage_array_index_access_bytes32_dyn__dyn
                 [Lit 2, Var "var_i"],
               LetCall ["_9", "_10"] storage_array_index_access_bytes32_dyn__dyn
                 [Lit 3, Var "var_i"],
               LetPrimCall ["split_expr_7"] .Sload [Var "_9"],
               LetCall ["split_expr_8"] extract_from_storage_value_dynamict_bytes32
                 [Var "split_expr_7", Var "_10"],
               ExprStmtCall array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
                 [Var "_7", Var "split_expr_8"]],
             .Block
              [AssignCall ["var_maxNodeNumber"] checked_div_uint256 [Var "var_maxNodeNumber"],
               AssignCall ["var_oldMaxNodeNumber"] checked_div_uint256 [Var "var_oldMaxNodeNumber"]]] : List Stmt)
        = _root_.L2InteropCommitmentTree.Common.for_5765234204941653661_body from rfl,
      show (Lit 1 : Expr)
        = _root_.L2InteropCommitmentTree.Common.for_5765234204941653661_cond from rfl]
  obtain ⟨σ', hσ'eq, hσ'pres⟩ := pad_loop k (fuel := fuel+1)
    (evm := evm)
    (σ := Finmap.insert "var_i" 0 (Finmap.insert "var_i" 0
      (Finmap.insert "var_maxNodeNumber" c
        (Finmap.insert "var_oldMaxNodeNumber" (c - 1) σ))))
    (i := 0) (om := c - 1) (m := c)
    (by exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    hcont hstop hpass (by omega)
  refine ⟨σ', hσ'eq, ?_⟩
  intro key hkey
  rw [hσ'pres key hkey]
  rw [lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide))]

/-- **P5 — CLOSED FORM OF `fun_pushNewLeaf` (non-growth path).**  The leaf
count is bumped, the tree is not at capacity (growth skipped), the frontier is
padded (`padWalk`), and the root recompute delegates to the proven
`updateLeaf` closed form (`updateWalk` over the leaf write). -/
theorem pushNewLeaf_call
    {evm : EVMState} {store : VarStore} {fuel k k2 : ℕ}
    {vleaf : Literal} {v : Identifier}
    (hcmax : evm.sload 1
      ≠ (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256))
    (hc0 : evm.sload 1 ≠ 0)
    (hnp : ¬ (evm.sload 1
      = Fin.shiftLeft 1 ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)))
    -- the padding pack (over the post-increment evm)
    (hcont : ∀ j, j < k →
      (padWalk j (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).2.1
          < (padWalk j (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload 0
        ∧ (padWalk j (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).2.2.1
          ≠ (padWalk j (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).2.2.2)
    (hstop : ¬ ((padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).2.1
          < (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload 0)
      ∨ (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).2.2.1
          = (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).2.2.2)
    (hpass : ∀ j, j < k →
      PadOK (padWalk j (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)))
    -- the updateLeaf pack (over the post-padding evm)
    (hsub0 : (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
        ((0 : UInt256) + 1) ≠ 0)
    (hle : ¬ (evm.sload 1
      > (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
          ((0 : UInt256) + 1) - 1))
    (hne2 : (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
        ((0 : UInt256) + 2) ≠ 0)
    (hbidx : evm.sload 1
      < (arrOut (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1
            ((0 : UInt256) + 2)).2.sload
          (arrOut (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1
            ((0 : UInt256) + 2)).1)
    (hk2 : ((leafWriteEvm
        (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1
        0 (evm.sload 1) vleaf).sload 0).val = k2)
    (hpass2 : ∀ j, j < k2 → WalkOK 0 ((0 : UInt256) + 2)
        (updateWalk 0 ((0 : UInt256) + 2) j
          (leafWriteEvm
            (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1
            0 (evm.sload 1) vleaf)
          0 (evm.sload 1)
          ((padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
            ((0 : UInt256) + 1) - 1) vleaf))
    (hssinv2 : ∀ j, j ≤ k2 →
        ((updateWalk 0 ((0 : UInt256) + 2) j
          (leafWriteEvm
            (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1
            0 (evm.sload 1) vleaf)
          0 (evm.sload 1)
          ((padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
            ((0 : UInt256) + 1) - 1) vleaf).1).sload 0
          = (leafWriteEvm
              (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1
              0 (evm.sload 1) vleaf).sload 0)
    (hfuelp : 2 * k + 2 ≤ fuel)
    (hfuelu : 2 * k2 + 2 ≤ fuel) :
    execCall (fuel+1) fun_pushNewLeaf [v] (Ok evm store, [vleaf])
      = Ok (updateWalk 0 ((0 : UInt256) + 2) k2
            (leafWriteEvm
              (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1
              0 (evm.sload 1) vleaf)
            0 (evm.sload 1)
            ((padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
              ((0 : UInt256) + 1) - 1) vleaf).1
          (store.insert v
            (updateWalk 0 ((0 : UInt256) + 2) k2
              (leafWriteEvm
                (padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1
                0 (evm.sload 1) vleaf)
              0 (evm.sload 1)
              ((padWalk k (evm.sstore 1 (evm.sload 1 + 1)) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
                ((0 : UInt256) + 1) - 1) vleaf).2.2.2.2) := by
  unfold execCall call fun_pushNewLeaf
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  set s0 := (Ok evm store)☎️⟦["var_leaf"], [vleaf]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["var_leaf"]!! = vleaf := by rw [hs0]; exact lookup_initcall_1
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq] at hp1 ⊢
  have hp1e : ∀ e : EVMState, (Ok e σ0)["var_leaf"]!! = vleaf := fun _ => hp1
  -- _1 := sload(1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  simp only [evm_Ok, insert_Ok]
  -- split_expr_0 := increment(_1)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [increment_call hcmax]
  -- sstore(1, split_expr_0)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSstore', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [evm_Ok]
  rw [show ∀ (e : EVMState) (σ' : VarStore) (e' : EVMState),
      ((Ok e σ' : State).setEvm e') = Ok e' σ' from fun _ _ _ => rfl]
  -- _2 := sload(0) ; split_expr_1 := shl(_2, 1)
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
             EVMShl', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [insert_Ok]
  -- the growth-if is skipped (not at capacity)
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMEq']
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [lookup_insert_self_fin]
  rw [show fromBool (evm.sload 1
      = Fin.shiftLeft 1 ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)) = (0 : UInt256) from by
    rw [decide_eq_false hnp]; rfl]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- split_expr_4 := iszero(_1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMIszero', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [show fromBool (evm.sload 1 = 0) = (0 : UInt256) from by
    rw [decide_eq_false hc0]; rfl]
  simp only [insert_Ok]
  -- the padding-if, folded to the named Common def
  rw [cons]
  try simp only [ptr_norm₁]
  rw [show (If (PrimCall .Iszero [Var "split_expr_4"])
        [LetCall ["var_oldMaxNodeNumber"] checked_sub_uint256 [Var "_1"],
         LetEq "var_maxNodeNumber" (Var "_1"),
         LetEq "var_i" (Lit 0),
         Assign "var_i" (Lit 0),
         For (Lit 1) [AssignPrimCall ["var_i"] .Add [Var "var_i", Lit 1]]
           [LetPrimCall ["split_expr_5"] .Sload [Lit 0],
            LetPrimCall ["split_expr_6"] .Lt [Var "var_i", Var "split_expr_5"],
            If (PrimCall .Iszero [Var "split_expr_6"]) [Stmt.Break],
            If (PrimCall .Eq [Var "var_oldMaxNodeNumber", Var "var_maxNodeNumber"]) [Stmt.Break],
            .Block
             [LetCall ["_7", "_8"] storage_array_index_access_bytes32_dyn__dyn
                [Lit 2, Var "var_i"],
              LetCall ["_9", "_10"] storage_array_index_access_bytes32_dyn__dyn
                [Lit 3, Var "var_i"],
              LetPrimCall ["split_expr_7"] .Sload [Var "_9"],
              LetCall ["split_expr_8"] extract_from_storage_value_dynamict_bytes32
                [Var "split_expr_7", Var "_10"],
              ExprStmtCall array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
                [Var "_7", Var "split_expr_8"]],
            .Block
             [AssignCall ["var_maxNodeNumber"] checked_div_uint256 [Var "var_maxNodeNumber"],
              AssignCall ["var_oldMaxNodeNumber"] checked_div_uint256 [Var "var_oldMaxNodeNumber"]]]])
      = L2InteropCommitmentTree.Common.if_3948411532618903895 from rfl]
  obtain ⟨σ', hσ'eq, hσ'pres⟩ := pad_if (fuel := fuel) (k := k)
    (evm := evm.sstore 1 (evm.sload 1 + 1))
    (σ := Finmap.insert "split_expr_4" 0
      (Finmap.insert "split_expr_1"
          (Fin.shiftLeft 1 ((evm.sstore 1 (evm.sload 1 + 1)).sload 0))
        (Finmap.insert "_2" ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)
          (Finmap.insert "split_expr_0" (evm.sload 1 + 1)
            (Finmap.insert "_1" (evm.sload 1) σ0)))))
    (c := evm.sload 1)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    (by exact lookup_insert_self_fin)
    hc0 hcont hstop hpass hfuelp
  rw [hσ'eq]
  -- var_newRoot := fun_updateLeaf(0, _1, var_leaf)
  rw [cons, nil, AssignCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [hσ'pres "_1" (by decide)]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [hσ'pres "var_leaf" (by decide)]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hp1e]
  rw [updateLeaf_call (k := k2) hsub0 hle hne2 hbidx hk2 hpass2 hssinv2 hfuelu]
  -- rets + call wrapper
  rw [lookup_insert_self_fin]
  rw [reviveJump_Ok]
  try simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  try simp only [multifill_cons, multifill_nil, insert_Ok]

/-! ## P6 — the growth branch, composed -/

/-- Stage composites of the growth branch. -/
def growE1 (σ : EVMState) (d : UInt256) : EVMState := σ.sstore 0 (d + 1)

def growSv (σ : EVMState) (d : UInt256) : UInt256 :=
  (arrOut (growE1 σ d) 3).2.sload ((arrOut (growE1 σ d) 3).1 + ((d + 1) - 1))

def growH (σ : EVMState) (d : UInt256) : UInt256 × EVMState :=
  accOut (arrOut (growE1 σ d) 3).2 (growSv σ d) (growSv σ d)

def growE2 (σ : EVMState) (d : UInt256) : EVMState :=
  pushEvm (growH σ d).2 3 (growH σ d).1

def growP (σ : EVMState) (d : UInt256) : UInt256 := (growE2 σ d).mload 64

def growE3 (σ : EVMState) (d : UInt256) : EVMState :=
  ((growE2 σ d).mstore 64 (growP σ d + 32)).mstore (growP σ d) (growH σ d).1

/-- The full growth effect. -/
def growEvm (σ : EVMState) (d : UInt256) : EVMState :=
  pushArrEvm (growE3 σ d) 2 (growP σ d)

/-- **The taken growth-if** equals `growEvm` (chunks A/B/C composed). -/
lemma grow_if
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {c p d : Literal}
    (h1 : (Ok evm σ)["_1"]!! = c)
    (hs1 : (Ok evm σ)["split_expr_1"]!! = p)
    (h2 : (Ok evm σ)["_2"]!! = d)
    (heq : c = p)
    (hd1 : d + 1 ≠ 0)
    (hb3 : (d + 1) - 1 < (growE1 evm d).sload 3)
    (hlen3 : (((growH evm d).2).sload 3).val < 18446744073709551616)
    (hacc3 : ((growH evm d).2.lookupAccount
        (growH evm d).2.execution_env.code_owner).isSome)
    (hfp : (growP evm d).val + 32 ≤ 18446744073709551615)
    (hlen2 : ((growE3 evm d).sload 2).val < 18446744073709551616)
    (hacc2 : ((growE3 evm d).lookupAccount
        (growE3 evm d).execution_env.code_owner).isSome)
    (hstale : ¬ ((1 : UInt256)
      < (arrOut ((growE3 evm d).sstore 2 ((growE3 evm d).sload 2 + 1)) 2).2.sload
          ((arrOut ((growE3 evm d).sstore 2 ((growE3 evm d).sload 2 + 1)) 2).1
            + (growE3 evm d).sload 2)))
    (hfuel : 5 ≤ fuel) :
    ∃ σg : VarStore,
      exec (fuel+1) L2InteropCommitmentTree.Common.if_1084122831851539501 (Ok evm σ)
        = Ok (growEvm evm d) σg
      ∧ ∀ key : Identifier,
          key ∉ (["expr", "split_expr_2", "_3", "_4", "split_expr_3", "_5",
            "expr_1", "size", "_6", "expr_mpos"] : List Identifier) →
          (Ok (growEvm evm d) σg)[key]!! = (Ok evm σ)[key]!! := by
  unfold _root_.L2InteropCommitmentTree.Common.if_1084122831851539501
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMEq']
  rw [h1, hs1]
  rw [show fromBool (c = p) = (1 : UInt256) from by rw [decide_eq_true heq]; rfl]
  try simp only [head', List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- chunk A
  rw [cons]
  rw [growA_block h2 hd1 (by exact hb3)]
  -- chunk B
  rw [cons]
  rw [growB_block (sv := growSv evm d)
    (by exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    (by exact hlen3)
    (by exact hacc3)]
  -- chunk C
  rw [cons, nil]
  rw [growC_block (h := (growH evm d).1)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    (by exact hfp)
    (by exact hlen2)
    (by exact hacc2)
    (by exact hstale)
    hfuel]
  refine ⟨_, rfl, ?_⟩
  intro key hkey
  rw [lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide)),
      lookup_insert_ne_fin (by intro he; exact hkey (by rw [he]; decide))]
  exact lookup_ok_evm

/-- The padding-phase start state on the growth path. -/
def pushGrowBase (evm : EVMState) : EVMState :=
  growEvm (evm.sstore 1 (evm.sload 1 + 1)) ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)

/-- **CLOSED FORM OF `fun_pushNewLeaf` (growth path).**  At capacity: the tree
grows one level (`growEvm`), the frontier is padded, and the root recompute
delegates to `updateLeaf`. -/
theorem pushNewLeaf_call_grow
    {evm : EVMState} {store : VarStore} {fuel k k2 : ℕ}
    {vleaf : Literal} {v : Identifier}
    (hcmax : evm.sload 1
      ≠ (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256))
    (hc0 : evm.sload 1 ≠ 0)
    (hcap : evm.sload 1
      = Fin.shiftLeft 1 ((evm.sstore 1 (evm.sload 1 + 1)).sload 0))
    -- the growth pack (over the post-increment evm, depth read from it)
    (hd1 : (evm.sstore 1 (evm.sload 1 + 1)).sload 0 + 1 ≠ 0)
    (hb3 : ((evm.sstore 1 (evm.sload 1 + 1)).sload 0 + 1) - 1
      < (growE1 (evm.sstore 1 (evm.sload 1 + 1)) ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)).sload 3)
    (hlen3 : (((growH (evm.sstore 1 (evm.sload 1 + 1))
        ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)).2).sload 3).val < 18446744073709551616)
    (hacc3 : (((growH (evm.sstore 1 (evm.sload 1 + 1))
        ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)).2).lookupAccount
        ((growH (evm.sstore 1 (evm.sload 1 + 1))
        ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)).2).execution_env.code_owner).isSome)
    (hfpg : ((growP (evm.sstore 1 (evm.sload 1 + 1))
        ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)).val) + 32 ≤ 18446744073709551615)
    (hlen2 : (((growE3 (evm.sstore 1 (evm.sload 1 + 1))
        ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)).sload 2).val) < 18446744073709551616)
    (hacc2 : (((growE3 (evm.sstore 1 (evm.sload 1 + 1))
        ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)).lookupAccount
        ((growE3 (evm.sstore 1 (evm.sload 1 + 1))
        ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)).execution_env.code_owner)).isSome))
    (hstaleg : ¬ ((1 : UInt256)
      < (arrOut ((growE3 (evm.sstore 1 (evm.sload 1 + 1))
              ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)).sstore 2
            ((growE3 (evm.sstore 1 (evm.sload 1 + 1))
              ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)).sload 2 + 1)) 2).2.sload
          ((arrOut ((growE3 (evm.sstore 1 (evm.sload 1 + 1))
                ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)).sstore 2
              ((growE3 (evm.sstore 1 (evm.sload 1 + 1))
                ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)).sload 2 + 1)) 2).1
            + (growE3 (evm.sstore 1 (evm.sload 1 + 1))
                ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)).sload 2)))
    -- the padding pack (over the post-growth evm)
    (hcont : ∀ j, j < k →
      (padWalk j (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).2.1
          < (padWalk j (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload 0
        ∧ (padWalk j (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).2.2.1
          ≠ (padWalk j (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).2.2.2)
    (hstop : ¬ ((padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).2.1
          < (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload 0)
      ∨ (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).2.2.1
          = (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).2.2.2)
    (hpassp : ∀ j, j < k →
      PadOK (padWalk j (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)))
    -- the updateLeaf pack (over the post-padding evm)
    (hsub0 : (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
        ((0 : UInt256) + 1) ≠ 0)
    (hle : ¬ (evm.sload 1
      > (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
          ((0 : UInt256) + 1) - 1))
    (hne2 : (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
        ((0 : UInt256) + 2) ≠ 0)
    (hbidx : evm.sload 1
      < (arrOut (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1
            ((0 : UInt256) + 2)).2.sload
          (arrOut (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1
            ((0 : UInt256) + 2)).1)
    (hk2 : ((leafWriteEvm
        (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1
        0 (evm.sload 1) vleaf).sload 0).val = k2)
    (hpass2 : ∀ j, j < k2 → WalkOK 0 ((0 : UInt256) + 2)
        (updateWalk 0 ((0 : UInt256) + 2) j
          (leafWriteEvm
            (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1
            0 (evm.sload 1) vleaf)
          0 (evm.sload 1)
          ((padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
            ((0 : UInt256) + 1) - 1) vleaf))
    (hssinv2 : ∀ j, j ≤ k2 →
        ((updateWalk 0 ((0 : UInt256) + 2) j
          (leafWriteEvm
            (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1
            0 (evm.sload 1) vleaf)
          0 (evm.sload 1)
          ((padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
            ((0 : UInt256) + 1) - 1) vleaf).1).sload 0
          = (leafWriteEvm
              (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1
              0 (evm.sload 1) vleaf).sload 0)
    (hfuelg : 5 ≤ fuel)
    (hfuelp : 2 * k + 2 ≤ fuel)
    (hfuelu : 2 * k2 + 2 ≤ fuel) :
    execCall (fuel+1) fun_pushNewLeaf [v] (Ok evm store, [vleaf])
      = Ok (updateWalk 0 ((0 : UInt256) + 2) k2
            (leafWriteEvm
              (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1
              0 (evm.sload 1) vleaf)
            0 (evm.sload 1)
            ((padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
              ((0 : UInt256) + 1) - 1) vleaf).1
          (store.insert v
            (updateWalk 0 ((0 : UInt256) + 2) k2
              (leafWriteEvm
                (padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1
                0 (evm.sload 1) vleaf)
              0 (evm.sload 1)
              ((padWalk k (pushGrowBase evm) 0 (evm.sload 1 - 1) (evm.sload 1)).1.sload
                ((0 : UInt256) + 1) - 1) vleaf).2.2.2.2) := by
  unfold execCall call fun_pushNewLeaf
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  set s0 := (Ok evm store)☎️⟦["var_leaf"], [vleaf]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["var_leaf"]!! = vleaf := by rw [hs0]; exact lookup_initcall_1
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq] at hp1 ⊢
  have hp1e : ∀ e : EVMState, (Ok e σ0)["var_leaf"]!! = vleaf := fun _ => hp1
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  simp only [evm_Ok, insert_Ok]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [increment_call hcmax]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSstore', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [evm_Ok]
  rw [show ∀ (e : EVMState) (σ' : VarStore) (e' : EVMState),
      ((Ok e σ' : State).setEvm e') = Ok e' σ' from fun _ _ _ => rfl]
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
             EVMShl', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [insert_Ok]
  -- the growth-if is TAKEN
  rw [cons]
  obtain ⟨σg, hgeq, hgpres⟩ := grow_if (fuel := fuel)
    (c := evm.sload 1)
    (p := Fin.shiftLeft 1 ((evm.sstore 1 (evm.sload 1 + 1)).sload 0))
    (d := (evm.sstore 1 (evm.sload 1 + 1)).sload 0)
    (evm := evm.sstore 1 (evm.sload 1 + 1))
    (σ := Finmap.insert "split_expr_1"
        (Fin.shiftLeft 1 ((evm.sstore 1 (evm.sload 1 + 1)).sload 0))
      (Finmap.insert "_2" ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)
        (Finmap.insert "split_expr_0" (evm.sload 1 + 1)
          (Finmap.insert "_1" (evm.sload 1) σ0))))
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    (by exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    hcap hd1 hb3 hlen3 hacc3 hfpg hlen2 hacc2 hstaleg hfuelg
  try simp only [ptr_norm₁]
  rw [show (If (PrimCall .Eq [Var "_1", Var "split_expr_1"])
        [.Block
          [LetCall ["expr"] fun_uncheckedInc [Var "_2"],
           ExprStmtPrimCall .Sstore [Lit 0, Var "expr"],
           LetCall ["split_expr_2"] checked_sub_uint256 [Var "expr"],
           LetCall ["_3", "_4"] storage_array_index_access_bytes32_dyn__dyn
             [Lit 3, Var "split_expr_2"],
           LetPrimCall ["split_expr_3"] .Sload [Var "_3"]],
         .Block
          [LetCall ["_5"] extract_from_storage_value_dynamict_bytes32
             [Var "split_expr_3", Var "_4"],
           LetCall ["expr_1"] fun_efficientHash [Var "_5", Var "_5"],
           ExprStmtCall array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
             [Lit 3, Var "expr_1"],
           LetEq "size" (Lit 0),
           LetEq "_6" (Lit 0)],
         .Block
          [Assign "_6" (Lit 0),
           Assign "size" (Lit 32),
           LetCall ["expr_mpos"] allocate_memory [Lit 32],
           ExprStmtPrimCall .Mstore [Var "expr_mpos", Var "expr_1"],
           ExprStmtCall array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr
             [Lit 2, Var "expr_mpos"]]])
      = L2InteropCommitmentTree.Common.if_1084122831851539501 from rfl]
  rw [hgeq]
  -- split_expr_4 := iszero(_1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMIszero', multifill_cons, multifill_nil]
  rw [hgpres "_1" (by decide)]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [show fromBool (evm.sload 1 = 0) = (0 : UInt256) from by
    rw [decide_eq_false hc0]; rfl]
  simp only [insert_Ok]
  -- the padding-if, folded to the named Common def
  rw [cons]
  try simp only [ptr_norm₁]
  rw [show (If (PrimCall .Iszero [Var "split_expr_4"])
        [LetCall ["var_oldMaxNodeNumber"] checked_sub_uint256 [Var "_1"],
         LetEq "var_maxNodeNumber" (Var "_1"),
         LetEq "var_i" (Lit 0),
         Assign "var_i" (Lit 0),
         For (Lit 1) [AssignPrimCall ["var_i"] .Add [Var "var_i", Lit 1]]
           [LetPrimCall ["split_expr_5"] .Sload [Lit 0],
            LetPrimCall ["split_expr_6"] .Lt [Var "var_i", Var "split_expr_5"],
            If (PrimCall .Iszero [Var "split_expr_6"]) [Stmt.Break],
            If (PrimCall .Eq [Var "var_oldMaxNodeNumber", Var "var_maxNodeNumber"]) [Stmt.Break],
            .Block
             [LetCall ["_7", "_8"] storage_array_index_access_bytes32_dyn__dyn
                [Lit 2, Var "var_i"],
              LetCall ["_9", "_10"] storage_array_index_access_bytes32_dyn__dyn
                [Lit 3, Var "var_i"],
              LetPrimCall ["split_expr_7"] .Sload [Var "_9"],
              LetCall ["split_expr_8"] extract_from_storage_value_dynamict_bytes32
                [Var "split_expr_7", Var "_10"],
              ExprStmtCall array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
                [Var "_7", Var "split_expr_8"]],
            .Block
             [AssignCall ["var_maxNodeNumber"] checked_div_uint256 [Var "var_maxNodeNumber"],
              AssignCall ["var_oldMaxNodeNumber"] checked_div_uint256 [Var "var_oldMaxNodeNumber"]]]])
      = L2InteropCommitmentTree.Common.if_3948411532618903895 from rfl]
  obtain ⟨σ', hσ'eq, hσ'pres⟩ := pad_if (fuel := fuel) (k := k)
    (evm := growEvm (evm.sstore 1 (evm.sload 1 + 1)) ((evm.sstore 1 (evm.sload 1 + 1)).sload 0))
    (σ := Finmap.insert "split_expr_4" 0 σg)
    (c := evm.sload 1)
    (by rw [lookup_insert_ne_fin (by decide)]
        rw [hgpres "_1" (by decide)]
        rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    (by exact lookup_insert_self_fin)
    hc0 hcont hstop hpassp hfuelp
  rw [hσ'eq]
  -- var_newRoot := fun_updateLeaf(0, _1, var_leaf)
  rw [cons, nil, AssignCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [hσ'pres "_1" (by decide)]
  rw [lookup_insert_ne_fin (by decide)]
  rw [hgpres "_1" (by decide)]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [hσ'pres "var_leaf" (by decide)]
  rw [lookup_insert_ne_fin (by decide)]
  rw [hgpres "var_leaf" (by decide)]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hp1e]
  rw [updateLeaf_call (k := k2)
    (evm := (padWalk k (growEvm (evm.sstore 1 (evm.sload 1 + 1))
        ((evm.sstore 1 (evm.sload 1 + 1)).sload 0)) 0 (evm.sload 1 - 1) (evm.sload 1)).1)
    (ss := 0) (idx := evm.sload 1) (leaf := vleaf)
    hsub0 hle hne2 hbidx hk2 hpass2 hssinv2 hfuelu]
  rw [lookup_insert_self_fin]
  rw [reviveJump_Ok]
  try simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  try simp only [multifill_cons, multifill_nil, insert_Ok]
  rw [show pushGrowBase evm = growEvm (evm.sstore 1 (evm.sload 1 + 1))
      ((evm.sstore 1 (evm.sload 1 + 1)).sload 0) from rfl]

/-! ## The pool invariants cross the PADDING walk

`padWalk_lookup_mono` carries cache HITS across the padding loop; these carry the three
properties the derived separation route consumes.  Both are needed together: a hit is
useless to `cached_off_ne_off` without `Separated` and `CacheInj` in the same state.

The padding step is all `arrOut` and `sstore` — `pushEvm` is two stores around one array
hash — so each proof is a straight composition of the atom lemmas, then an induction on
the level count. -/

lemma separated_pushEvm {σ : EVMState} {arr v : UInt256}
    (h : Clear.KeccakSlotSep.Separated σ) :
    Clear.KeccakSlotSep.Separated (pushEvm σ arr v) := by
  unfold pushEvm
  exact Clear.StorageFrame.separated_sstore
    (separated_arrOut (Clear.StorageFrame.separated_sstore h))

lemma cacheInUsed_pushEvm {σ : EVMState} {arr v : UInt256}
    (h : Clear.KeccakFresh.CacheInUsed σ) :
    Clear.KeccakFresh.CacheInUsed (pushEvm σ arr v) := by
  unfold pushEvm
  exact Clear.StorageFrame.cacheInUsed_sstore
    (cacheInUsed_arrOut (Clear.StorageFrame.cacheInUsed_sstore h))

lemma cacheInj_pushEvm {σ : EVMState} {arr v : UInt256}
    (hu : Clear.KeccakFresh.CacheInUsed σ) (h : Clear.KeccakFresh.CacheInj σ) :
    Clear.KeccakFresh.CacheInj (pushEvm σ arr v) := by
  unfold pushEvm
  exact Clear.StorageFrame.cacheInj_sstore
    (cacheInj_arrOut (Clear.StorageFrame.cacheInUsed_sstore hu)
      (Clear.StorageFrame.cacheInj_sstore h))

lemma separated_padStep {σ : EVMState} {i : UInt256}
    (h : Clear.KeccakSlotSep.Separated σ) :
    Clear.KeccakSlotSep.Separated (padStep σ i) := by
  unfold padStep
  exact separated_pushEvm (separated_arrOut (separated_arrOut h))

lemma cacheInUsed_padStep {σ : EVMState} {i : UInt256}
    (h : Clear.KeccakFresh.CacheInUsed σ) :
    Clear.KeccakFresh.CacheInUsed (padStep σ i) := by
  unfold padStep
  exact cacheInUsed_pushEvm (cacheInUsed_arrOut (cacheInUsed_arrOut h))

lemma cacheInj_padStep {σ : EVMState} {i : UInt256}
    (hu : Clear.KeccakFresh.CacheInUsed σ) (h : Clear.KeccakFresh.CacheInj σ) :
    Clear.KeccakFresh.CacheInj (padStep σ i) := by
  unfold padStep
  exact cacheInj_pushEvm (cacheInUsed_arrOut (cacheInUsed_arrOut hu))
    (cacheInj_arrOut (cacheInUsed_arrOut hu) (cacheInj_arrOut hu h))

/-- **The padding walk preserves slot separation** (`padWalk_lookup_mono` twin). -/
lemma separated_padWalk :
    ∀ (k : ℕ) {σ : EVMState} {i om m : UInt256},
    Clear.KeccakSlotSep.Separated σ →
    Clear.KeccakSlotSep.Separated ((padWalk k σ i om m).1) := by
  intro k
  induction k with
  | zero => intro σ _ _ _ h; exact h
  | succ k ih =>
    intro σ i om m h
    simp only [padWalk]
    exact ih (separated_padStep h)

/-- **The padding walk preserves cache-in-used.** -/
lemma cacheInUsed_padWalk :
    ∀ (k : ℕ) {σ : EVMState} {i om m : UInt256},
    Clear.KeccakFresh.CacheInUsed σ →
    Clear.KeccakFresh.CacheInUsed ((padWalk k σ i om m).1) := by
  intro k
  induction k with
  | zero => intro σ _ _ _ h; exact h
  | succ k ih =>
    intro σ i om m h
    simp only [padWalk]
    exact ih (cacheInUsed_padStep h)

/-- **The padding walk preserves cache injectivity.** -/
lemma cacheInj_padWalk :
    ∀ (k : ℕ) {σ : EVMState} {i om m : UInt256},
    Clear.KeccakFresh.CacheInUsed σ → Clear.KeccakFresh.CacheInj σ →
    Clear.KeccakFresh.CacheInj ((padWalk k σ i om m).1) := by
  intro k
  induction k with
  | zero => intro σ _ _ _ _ h; exact h
  | succ k ih =>
    intro σ i om m hu h
    simp only [padWalk]
    exact ih (cacheInUsed_padStep hu) (cacheInj_padStep hu h)

/-! ## The low-slot window config crosses the padding walk

Same shape as the pool invariants above, for the pair
`keccak256_add_ne_lowSlot_of_config` consumes. -/

lemma rangeInWindow_pushEvm {σ : EVMState} {arr v : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ) :
    Clear.KeccakLowSlot.RangeInWindow (pushEvm σ arr v) := by
  unfold pushEvm
  exact Clear.StorageFrame.rangeInWindow_sstore
    (rangeInWindow_arrOut (Clear.StorageFrame.rangeInWindow_sstore hR))

lemma cachedInWindow_pushEvm {σ : EVMState} {arr v : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ)
    (hC : Clear.KeccakLowSlot.CachedInWindow σ) :
    Clear.KeccakLowSlot.CachedInWindow (pushEvm σ arr v) := by
  unfold pushEvm
  exact Clear.StorageFrame.cachedInWindow_sstore
    (cachedInWindow_arrOut (Clear.StorageFrame.rangeInWindow_sstore hR)
      (Clear.StorageFrame.cachedInWindow_sstore hC))

lemma rangeInWindow_padStep {σ : EVMState} {i : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ) :
    Clear.KeccakLowSlot.RangeInWindow (padStep σ i) := by
  unfold padStep
  exact rangeInWindow_pushEvm (rangeInWindow_arrOut (rangeInWindow_arrOut hR))

lemma cachedInWindow_padStep {σ : EVMState} {i : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ)
    (hC : Clear.KeccakLowSlot.CachedInWindow σ) :
    Clear.KeccakLowSlot.CachedInWindow (padStep σ i) := by
  unfold padStep
  exact cachedInWindow_pushEvm (rangeInWindow_arrOut (rangeInWindow_arrOut hR))
    (cachedInWindow_arrOut (rangeInWindow_arrOut hR)
      (cachedInWindow_arrOut hR hC))

/-- **The padding walk keeps the pool inside the window.** -/
lemma rangeInWindow_padWalk :
    ∀ (k : ℕ) {σ : EVMState} {i om m : UInt256},
    Clear.KeccakLowSlot.RangeInWindow σ →
    Clear.KeccakLowSlot.RangeInWindow ((padWalk k σ i om m).1) := by
  intro k
  induction k with
  | zero => intro σ _ _ _ h; exact h
  | succ k ih =>
    intro σ i om m h
    simp only [padWalk]
    exact ih (rangeInWindow_padStep h)

/-- **The padding walk keeps the cache inside the window.** -/
lemma cachedInWindow_padWalk :
    ∀ (k : ℕ) {σ : EVMState} {i om m : UInt256},
    Clear.KeccakLowSlot.RangeInWindow σ → Clear.KeccakLowSlot.CachedInWindow σ →
    Clear.KeccakLowSlot.CachedInWindow ((padWalk k σ i om m).1) := by
  intro k
  induction k with
  | zero => intro σ _ _ _ _ h; exact h
  | succ k ih =>
    intro σ i om m hR hC
    simp only [padWalk]
    exact ih (rangeInWindow_padStep hR) (cachedInWindow_padStep hR hC)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
