import Clear.ReasoningPrinciple

import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_push_user
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_5765234204941653661
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_1084122831851539501
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_hash_user

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

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
