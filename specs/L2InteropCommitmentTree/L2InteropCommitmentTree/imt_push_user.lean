import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_uncheckedInc
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.allocate_memory
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_dataslot_array_array_bytes32_dyn_storage_dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation
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

private lemma mkOk_Ok {e : EVMState} {σ : VarStore} : 👌 (Ok e σ) = Ok e σ := rfl

private lemma reviveJump_Ok {e : EVMState} {σ : VarStore} : 🧟 (Ok e σ) = Ok e σ := rfl

private lemma reviveJump_of_isOk {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma evm_setEvm_of_isOk {s : State} {e : EVMState} (h : isOk s) :
    (s.setEvm e).evm = e := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma lookup_setEvm_of_isOk {s : State} {e : EVMState} {k : Identifier}
    (h : isOk s) : (s.setEvm e)[k]!! = s[k]!! := by
  obtain ⟨evm₀, st, rfl⟩ := State_of_isOk h; rfl

private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok]; exact lookup_insert_of_ne h

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

private lemma primCall_keccakOut {s : State} {a b : Literal} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (keccakOut s.evm a b).2, [(keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

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

private lemma val_add_32 {p : UInt256} (hp : p.val + 32 ≤ 18446744073709551615) :
    ((p + (32 : UInt256))).val = p.val + 32 := by
  have h32 : ((32 : UInt256)).val = 32 := by decide
  have hlt : p.val + ((32 : UInt256)).val < UInt256.size := by
    have hs : UInt256.size = 2 ^ 256 := by norm_num
    omega
  calc ((p + (32 : UInt256))).val
      = (p.val + ((32 : UInt256)).val) % UInt256.size := rfl
    _ = p.val + ((32 : UInt256)).val := Nat.mod_eq_of_lt hlt
    _ = p.val + 32 := by rw [h32]

lemma finalize_allocation_32_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {p : Literal}
    (hp : p.val + 32 ≤ 18446744073709551615) :
    execCall (fuel+1) finalize_allocation [] (Ok evm store, [p, 32])
      = (Ok evm store).setEvm (evm.mstore 64 (p + 32)) := by
  unfold execCall call finalize_allocation
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  simp only [cons, nil]
  simp only [If', LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMAdd', EVMNot', EVMAnd', EVMGt', EVMLt', EVMOr', EVMMstore']
  simp only [multifill_cons, multifill_nil]
  set B := (Ok evm store)☎️⟦["memPtr", "size"], [p, 32]⟧ with hB
  have hokB : isOk B := isOk_initcall_of_isOk trivial
  have l_size : B["size"]!! = 32 := lookup_initcall_2 (by decide)
  have l_mem : B["memPtr"]!! = p := lookup_initcall_1
  rw [l_size]
  rw [show ((32 : UInt256) + 31) = 63 from by decide]
  set m31 := Clear.UInt256.lnot 31 with hm31
  have hok0 : isOk (B⟦"split_expr_0" ↦ 63⟧) := isOk_insert.mpr hokB
  have hok1 : isOk (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧) := isOk_insert.mpr hok0
  have l0 : (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧)["split_expr_0"]!! = 63 := by
    rw [lookup_insert_of_ne (by decide), lookup_insert' hokB]
  have l1 : (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧)["split_expr_1"]!! = m31 :=
    lookup_insert' hok0
  rw [l0, l1]
  have hland : Fin.land 63 m31 = (32 : UInt256) := by
    rw [hm31]; decide
  rw [hland]
  have l_mem2 : (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (32 : UInt256)⟧)["memPtr"]!!
      = p := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
        lookup_insert_of_ne (by decide)]
    exact l_mem
  have hok2 : isOk (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (32 : UInt256)⟧) :=
    isOk_insert.mpr hok1
  have l2 : (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (32 : UInt256)⟧)["split_expr_2"]!!
      = 32 := lookup_insert' hok1
  rw [l_mem2, l2]
  -- the two guards evaluate to 0 given `hp`
  have hMAXv : ((18446744073709551615 : UInt256)).val = 18446744073709551615 := by decide
  have hgt : fromBool (p + 32 > (18446744073709551615 : UInt256)) = (0 : UInt256) := by
    rw [decide_eq_false (by
      intro h
      rw [gt_iff_lt, Fin.lt_def, hMAXv, val_add_32 hp] at h
      omega)]
    rfl
  have hlt : fromBool (p + 32 < p) = (0 : UInt256) := by
    rw [decide_eq_false (by
      intro h
      rw [Fin.lt_def, val_add_32 hp] at h
      omega)]
    rfl
  -- resolve the newFreePtr binding, then the two guard values
  have hok3 : isOk (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (32 : UInt256)⟧⟦"newFreePtr" ↦ p + 32⟧) :=
    isOk_insert.mpr hok2
  have lnf : (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (32 : UInt256)⟧⟦"newFreePtr" ↦ p + 32⟧)["newFreePtr"]!!
      = p + 32 := lookup_insert' hok2
  rw [lnf, hgt]
  have hok4 : isOk (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (32 : UInt256)⟧⟦"newFreePtr" ↦ p + 32⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧) :=
    isOk_insert.mpr hok3
  have l3nf : (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (32 : UInt256)⟧⟦"newFreePtr" ↦ p + 32⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧)["newFreePtr"]!!
      = p + 32 := by
    rw [lookup_insert_of_ne (by decide)]; exact lnf
  have l3mem : (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (32 : UInt256)⟧⟦"newFreePtr" ↦ p + 32⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧)["memPtr"]!!
      = p := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]; exact l_mem2
  rw [l3nf, l3mem, hlt]
  -- the guard `or` is 0: skip the panic branch
  have l4a : (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (32 : UInt256)⟧⟦"newFreePtr" ↦ p + 32⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)["split_expr_3"]!!
      = 0 := by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_insert' hok3
  have l4b : (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (32 : UInt256)⟧⟦"newFreePtr" ↦ p + 32⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)["split_expr_4"]!!
      = 0 := lookup_insert' hok4
  rw [l4a, l4b]
  rw [show Fin.lor (0 : UInt256) 0 = (0 : UInt256) from by decide]
  simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  -- trailing mstore(64, newFreePtr) on the else-branch state
  have hok5 : isOk (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (32 : UInt256)⟧⟦"newFreePtr" ↦ p + 32⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧) :=
    isOk_insert.mpr hok4
  have l5nf : (B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (32 : UInt256)⟧⟦"newFreePtr" ↦ p + 32⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)["newFreePtr"]!!
      = p + 32 := by
    rw [lookup_insert_of_ne (by decide)]; exact l3nf
  rw [l5nf]
  have hBevm : B.evm = evm := by
    rw [hB]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  simp only [evm_insert, evm_Ok]
  rw [hBevm]
  have hin_ok : isOk ((B⟦"split_expr_0" ↦ 63⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (32 : UInt256)⟧⟦"newFreePtr" ↦ p + 32⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)🇪⟦evm.mstore 64 (p + 32)⟧) := by
    rw [isOk_setEvm]; exact hok5
  rw [reviveJump_of_isOk hin_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = evm.mstore 64 (p + 32) := by
    have h := congrArg State.evm hi
    rw [evm_setEvm_of_isOk hok5] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]
  rfl



/-- **Closed form of `allocate_memory(32)`**: returns the free pointer and
bumps it by 32. -/
lemma allocate_memory_32_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {v : Identifier}
    (hp : (evm.mload 64).val + 32 ≤ 18446744073709551615) :
    execCall (fuel+1) allocate_memory [v] (Ok evm store, [32])
      = Ok (evm.mstore 64 (evm.mload 64 + 32))
          (Finmap.insert v (evm.mload 64) store) := by
  unfold execCall call allocate_memory
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  set s0 := (Ok evm store)☎️⟦["size"], [32]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["size"]!! = 32 := by rw [hs0]; exact lookup_initcall_1
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq] at hp1 ⊢
  rw [cons, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMMload', multifill_cons, multifill_nil]
  simp only [evm_Ok, insert_Ok]
  rw [cons, nil, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), hp1]
  rw [finalize_allocation_32_call hp]
  simp only [setEvm_Ok]
  rw [lookup_insert_self_fin]
  rw [reviveJump_of_isOk (by trivial)]
  try simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  try simp only [multifill_cons, multifill_nil, insert_Ok]



/-- Closed form of `array_dataslot(ptr)`: `keccak(ptr)` (one `arrOut` step). -/
lemma dataslot_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {ptr : Literal} {v : Identifier} :
    execCall (fuel+1) array_dataslot_array_array_bytes32_dyn_storage_dyn [v]
        (Ok evm store, [ptr])
      = Ok (arrOut evm ptr).2 (Finmap.insert v (arrOut evm ptr).1 store) := by
  unfold execCall call array_dataslot_array_array_bytes32_dyn_storage_dyn
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  set s0 := (Ok evm store)☎️⟦["ptr"], [ptr]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["ptr"]!! = ptr := by rw [hs0]; exact lookup_initcall_1
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq] at hp1 ⊢
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMMstore', multifill_cons, multifill_nil]
  rw [hp1]
  simp only [evm_Ok, setEvm_Ok]
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append]
  rw [primCall_keccakOut]
  simp only [evm_Ok, setEvm_Ok, multifill_cons, multifill_nil]
  rw [show keccakOut (evm.mstore 0 ptr) 0 32 = arrOut evm ptr from rfl]
  simp only [insert_Ok]
  rw [lookup_insert_self_fin]
  rw [reviveJump_of_isOk (by trivial)]
  try simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  try simp only [multifill_cons, multifill_nil, insert_Ok]



/-- The arrays-of-arrays push effect: bump the outer length, set the new
element's inner length to 1, copy the single value from memory. -/
def pushArrEvm (σ : EVMState) (arr src : UInt256) : EVMState :=
  let E1 := σ.sstore arr (σ.sload arr + 1)
  let sl := (arrOut E1 arr).1 + σ.sload arr
  let E3 := (arrOut E1 arr).2.sstore sl 1
  let B := arrOut E3 sl
  B.2.sstore B.1 (B.2.mload src)

/-- **Closed form of the arrays-of-arrays push** (length below `2⁶⁴`, contract
account exists, the fresh slot holds no long stale array): push a length-1
level array whose single element is read from memory at `src`. -/
lemma array_push_array_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {arr src : Literal}
    (hlen : (evm.sload arr).val < 18446744073709551616)
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome)
    (hstale : ¬ ((1 : UInt256)
      < (arrOut (evm.sstore arr (evm.sload arr + 1)) arr).2.sload
          ((arrOut (evm.sstore arr (evm.sload arr + 1)) arr).1 + evm.sload arr)))
    (hfuel : 5 ≤ fuel) :
    execCall (fuel+1) array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr []
        (Ok evm store, [arr, src])
      = Ok (pushArrEvm evm arr src) store := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have hlen1 : (evm.sload arr + 1).val = (evm.sload arr).val + 1 := by
    rw [Fin.val_add, show ((1 : UInt256)).val = 1 from by decide]
    exact Nat.mod_eq_of_lt (by omega)
  have hlen1nz : evm.sload arr + 1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    rw [hlen1, show ((0 : UInt256)).val = 0 from by decide] at this
    omega
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 5 := ⟨fuel - 5, by omega⟩
  unfold execCall call array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  set s0 := (Ok evm store)☎️⟦["array", "value0"], [arr, src]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["array"]!! = arr := by rw [hs0]; exact lookup_initcall_1
  have hp2 : s0["value0"]!! = src := by rw [hs0]; exact lookup_initcall_2 (by decide)
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq] at hp1 hp2 ⊢
  have hp1e : ∀ e : EVMState, (Ok e σ0)["array"]!! = arr := fun _ => hp1
  have hp2e : ∀ e : EVMState, (Ok e σ0)["value0"]!! = src := fun _ => hp2
  -- oldLen := sload(array)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [hp1]
  simp only [insert_Ok]
  rw [show ∀ σ' : VarStore, (Ok evm σ').evm = evm from fun _ => rfl]
  -- split_expr_0 := lt(oldLen, 2^64) = 1; guard skipped
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
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- split_expr_1 := add(oldLen, 1); sstore(array, split_expr_1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMAdd', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  simp only [insert_Ok]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSstore', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hp1]
  simp only [evm_Ok, setEvm_Ok]
  -- (slot, offset) := arrayaccess(array, oldLen)
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
  -- if offset {…} — offset = 0, skipped
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', Lit', Var',
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- oldLen_1 := sload(slot); sstore(slot, 1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [evm_Ok, insert_Ok]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSstore', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  simp only [evm_Ok, setEvm_Ok]
  -- if lt(1, oldLen_1) — skipped (no stale long array)
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMLt']
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256)
      < (arrOut (evm.sstore arr (evm.sload arr + 1)) arr).2.sload
          ((arrOut (evm.sstore arr (evm.sload arr + 1)) arr).1 + evm.sload arr))
      = (0 : UInt256) from by rw [decide_eq_false hstale]; rfl]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- srcPtr := value0 ; dstSlot := dataslot(slot) ; i := 0
  rw [cons, LetEq']
  simp only [Var']
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hp2e]
  simp only [insert_Ok]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [dataslot_call]
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  -- the copy loop: exactly one iteration
  rw [cons, nil]
  rw [For']
  dsimp only
  simp only [eval, evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMLt',
             mkOk_Ok]
  rw [lookup_insert_self_fin]
  rw [show fromBool ((0 : UInt256) < 1) = (1 : UInt256) from by decide]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((1 : UInt256) = 0))]
  -- iteration 1 body: mload / bump srcPtr / slot arith / sstore
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMMload', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  simp only [evm_Ok, insert_Ok]
  rw [cons, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMAdd', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  simp only [insert_Ok]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMAdd', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  simp only [add_zero, insert_Ok]
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSstore', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  simp only [evm_Ok, setEvm_Ok]
  -- select the continue arm, run the post, exit on the next check
  try dsimp only
  rw [reviveJump_Ok]
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMAdd', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [show ((0 : UInt256) + 1) = (1 : UInt256) from by decide]
  simp only [insert_Ok]
  try simp only [overwrite?_of_Ok]
  rw [For']
  dsimp only
  simp only [eval, evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMLt', mkOk_Ok]
  rw [lookup_insert_self_fin]
  rw [show fromBool ((1 : UInt256) < 1) = (0 : UInt256) from by decide]
  try simp only [head', List.head!]
  try simp only [if_true]
  try simp only [overwrite?_of_Ok]
  -- call wrapper (no rets)
  rw [reviveJump_of_isOk (by trivial)]
  try simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  try simp only [multifill_nil]
  rfl

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
