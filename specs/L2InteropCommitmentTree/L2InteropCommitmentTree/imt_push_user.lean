import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_uncheckedInc
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.increment_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_storage_atoms_user
import specs.AtomicFlowManager.AtomicFlowManager.no_double_refund_user

/-
  P1 — atoms of the `fun_pushNewLeaf` append path.

  * `uncheckedInc_call` — `x + 1`, unchecked.
  * `increment_call` — `x + 1` with the max-guard skipped.
  * `array_push_call` — the storage-array push: bump the length slot, write the
    value at the old tail (`pushEvm`).

  Axiom-free (the same-slot read-back uses the proven
  `sload_sstore_self_of_nonzero`, with the standard contract-account-exists
  hypothesis `hacc`).
-/

namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism

set_option maxRecDepth 6000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

private lemma insert_Ok {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

private lemma evm_Ok {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

private lemma setEvm_Ok {e e' : EVMState} {σ : VarStore} :
    (Ok e σ).setEvm e' = Ok e' σ := rfl

private lemma reviveJump_of_isOk {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok]; exact lookup_insert_of_ne h

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

/-- Closed form of `fun_uncheckedInc(x)`: `x + 1`. -/
lemma uncheckedInc_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x : Literal} {v : Identifier} :
    execCall (fuel+1) fun_uncheckedInc [v] (Ok evm store, [x])
      = Ok evm (Finmap.insert v (x + 1) store) := by
  unfold execCall call fun_uncheckedInc
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMAdd', multifill_cons, multifill_nil]
  rw [lookup_initcall_1]
  have hok0 : isOk ((Ok evm store)☎️⟦["var_number"], [x]⟧) := isOk_initcall_of_isOk trivial
  rw [lookup_insert' hok0]
  rw [reviveJump_of_isOk (by rw [isOk_insert]; exact hok0)]
  try simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk (show isOk ((Ok evm store)☎️⟦["var_number"], [x]⟧⟦"var_" ↦ x + 1⟧)
    from by rw [isOk_insert]; exact hok0)
  have hi_evm : ei = evm := by
    have h := congrArg State.evm hi
    simp only [evm_insert] at h
    rw [show ((Ok evm store)☎️⟦["var_number"], [x]⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]
  try simp only [multifill_cons, multifill_nil, insert_Ok]

/-- Closed form of `increment_uint256(x)` (`x` below the max): `x + 1`. -/
lemma increment_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x : Literal} {v : Identifier}
    (hx : x ≠ (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256)) :
    execCall (fuel+1) increment_uint256 [v] (Ok evm store, [x])
      = Ok evm (Finmap.insert v (x + 1) store) := by
  unfold execCall call increment_uint256
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  set s0 := (Ok evm store)☎️⟦["value"], [x]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["value"]!! = x := by rw [hs0]; exact lookup_initcall_1
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
             EVMNot', multifill_cons, multifill_nil, insert_Ok]
  rw [show (UInt256.lnot 0 : UInt256)
      = (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256)
    from by decide]
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMEq']
  rw [lookup_insert_ne_fin (by decide), hp1]
  rw [lookup_insert_self_fin]
  rw [show fromBool (x = (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256))
      = (0 : UInt256) from by rw [decide_eq_false hx]; rfl]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMAdd', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hp1]
  simp only [insert_Ok]
  rw [lookup_insert_self_fin]
  rw [reviveJump_of_isOk (by trivial)]
  try simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  try simp only [multifill_cons, multifill_nil, insert_Ok]

/-- The push effect: bump the length slot, write at the old tail. -/
def pushEvm (σ : EVMState) (arr v : UInt256) : EVMState :=
  (arrOut (σ.sstore arr (σ.sload arr + 1)) arr).2.sstore
    ((arrOut (σ.sstore arr (σ.sload arr + 1)) arr).1 + σ.sload arr) v

/-- **Closed form of the storage-array push** (length below `2⁶⁴`, contract
account exists): bump the length, store the value at the old tail. -/
lemma array_push_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {arr v : Literal}
    (hlen : (evm.sload arr).val < 18446744073709551616)
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome) :
    execCall (fuel+1) array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr []
        (Ok evm store, [arr, v])
      = Ok (pushEvm evm arr v) store := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have hlen1 : (evm.sload arr + 1).val = (evm.sload arr).val + 1 := by
    rw [Fin.val_add, show ((1 : UInt256)).val = 1 from by decide]
    exact Nat.mod_eq_of_lt (by omega)
  have hlen1nz : evm.sload arr + 1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    rw [hlen1, show ((0 : UInt256)).val = 0 from by decide] at this
    omega
  unfold execCall call array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  set s0 := (Ok evm store)☎️⟦["array", "value0"], [arr, v]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["array"]!! = arr := by rw [hs0]; exact lookup_initcall_1
  have hp2 : s0["value0"]!! = v := by rw [hs0]; exact lookup_initcall_2 (by decide)
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq] at hp1 hp2 ⊢
  have hp1e : ∀ e : EVMState, (Ok e σ0)["array"]!! = arr := fun _ => hp1
  have hp2e : ∀ e : EVMState, (Ok e σ0)["value0"]!! = v := fun _ => hp2
  -- oldLen := sload(array)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [hp1]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  -- split_expr_0 := lt(oldLen, 2^64) = 1
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMLt', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [show fromBool (evm.sload arr < (18446744073709551616 : UInt256)) = (1 : UInt256) from by
    rw [decide_eq_true (by
      rw [Fin.lt_def, show ((18446744073709551616 : UInt256)).val = 18446744073709551616 from by decide]
      exact hlen)]; rfl]
  simp only [insert_Ok]
  -- the overflow guard is skipped
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- split_expr_1 := add(oldLen, 1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMAdd', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  simp only [insert_Ok]
  -- sstore(array, split_expr_1)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSstore', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hp1]
  simp only [evm_Ok, setEvm_Ok]
  -- (slot, offset) := arrayaccess(array, oldLen) — in-bounds on the bumped length
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hp1e]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [storage_array_index_call (by
    rw [generated.AtomicFlowManager.AtomicFlowManager.sload_sstore_self_of_nonzero evm arr _ hlen1nz hacc]
    rw [Fin.lt_def, hlen1]
    omega)]
  -- update_storage(slot, offset, value0)
  rw [cons, nil, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hp2e]
  rw [update_storage_call_0]
  rw [reviveJump_of_isOk (by trivial)]
  try simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  try simp only [multifill_nil]
  rfl

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
