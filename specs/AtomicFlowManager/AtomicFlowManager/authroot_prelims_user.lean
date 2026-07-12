import Clear.ReasoningPrinciple

import specs.AtomicFlowManager.AtomicFlowManager.imt_leafhash_user
import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_uint16
import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_address
import generated.AtomicFlowManager.AtomicFlowManager.allocate_memory_7476
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_bytes32
import generated.AtomicFlowManager.AtomicFlowManager.constant_L2_INTEROP_COMMITMENT_TREE_ADDR
import generated.AtomicFlowManager.AtomicFlowManager.cleanup_address

/-
  `authenticateRoot` PRELUDE HELPERS — closed forms.

  The root-authentication function builds the `L2Message` struct (tx number,
  the pinned commitment-tree sender address, the abi-encoded root payload)
  before the verification staticcall.  This file closes the six small
  helpers that construction uses: the masked memory writers, the fixed-96
  allocator, the single-word abi encoder, the pinned sender constant, and
  the address cleaner.  Building blocks for stitching the #38 guards through
  the full `fun_authenticateRoot` body.

  Axiom-free.
-/

namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-! ### Local state-plumbing helpers -/

@[simp] private lemma insert_Ok {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

private lemma evm_Ok {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

private lemma setEvm_Ok {e E : EVMState} {σ : VarStore} :
    (Ok e σ).setEvm E = Ok E σ := rfl

private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok]; exact lookup_insert_of_ne h

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

private lemma evm_setEvm_of_isOk {s : State} {e : EVMState} (h : isOk s) :
    (s.setEvm e).evm = e := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma reviveJump_of_isOk {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma lookup_setEvm_of_isOk {s : State} {e : EVMState} {k : Identifier}
    (h : isOk s) : (s.setEvm e)[k]!! = s[k]!! := by
  obtain ⟨evm₀, st, rfl⟩ := State_of_isOk h; rfl

private lemma val_add_96 {p : UInt256} (hp : p.val + 96 ≤ 18446744073709551615) :
    ((p + (96 : UInt256))).val = p.val + 96 := by
  have h96 : ((96 : UInt256)).val = 96 := by decide
  have hlt : p.val + ((96 : UInt256)).val < UInt256.size := by
    have hs : UInt256.size = 2 ^ 256 := by norm_num
    omega
  calc ((p + (96 : UInt256))).val
      = (p.val + ((96 : UInt256)).val) % UInt256.size := rfl
    _ = p.val + ((96 : UInt256)).val := Nat.mod_eq_of_lt hlt
    _ = p.val + 96 := by rw [h96]

/-! ### The generic finalizer at size 96 -/

/-- `finalize_allocation(p, 96)`: the rounding is the identity and, under the
pointer bound, the call is exactly `mstore(64, p + 96)`. -/
lemma finalize_allocation_96'_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {p : Literal}
    (hp : p.val + 96 ≤ 18446744073709551615) :
    execCall (fuel+1) finalize_allocation [] (Ok evm store, [p, 96])
      = (Ok evm store).setEvm (evm.mstore 64 (p + 96)) := by
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
  set B := (Ok evm store)☎️⟦["memPtr", "size"], [p, 96]⟧ with hB
  have hokB : isOk B := isOk_initcall_of_isOk trivial
  have l_size : B["size"]!! = 96 := lookup_initcall_2 (by decide)
  have l_mem : B["memPtr"]!! = p := lookup_initcall_1
  rw [l_size]
  rw [show ((96 : UInt256) + 31) = 127 from by decide]
  set m31 := Clear.UInt256.lnot 31 with hm31
  have hok0 : isOk (B⟦"split_expr_0" ↦ 127⟧) := isOk_insert.mpr hokB
  have hok1 : isOk (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧) := isOk_insert.mpr hok0
  have l0 : (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧)["split_expr_0"]!! = 127 := by
    rw [lookup_insert_of_ne (by decide), lookup_insert' hokB]
  have l1 : (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧)["split_expr_1"]!! = m31 :=
    lookup_insert' hok0
  rw [l0, l1]
  have hland : Fin.land 127 m31 = (96 : UInt256) := by
    rw [hm31]; decide
  rw [hland]
  have l_mem2 : (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧)["memPtr"]!!
      = p := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
        lookup_insert_of_ne (by decide)]
    exact l_mem
  have hok2 : isOk (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧) :=
    isOk_insert.mpr hok1
  have l2 : (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧)["split_expr_2"]!!
      = 96 := lookup_insert' hok1
  rw [l_mem2, l2]
  have hMAXv : ((18446744073709551615 : UInt256)).val = 18446744073709551615 := by decide
  have hgt : fromBool (p + 96 > (18446744073709551615 : UInt256)) = (0 : UInt256) := by
    rw [decide_eq_false (by
      intro h
      rw [gt_iff_lt, Fin.lt_def, hMAXv, val_add_96 hp] at h
      omega)]
    rfl
  have hlt : fromBool (p + 96 < p) = (0 : UInt256) := by
    rw [decide_eq_false (by
      intro h
      rw [Fin.lt_def, val_add_96 hp] at h
      omega)]
    rfl
  have hok3 : isOk (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧⟦"newFreePtr" ↦ p + 96⟧) :=
    isOk_insert.mpr hok2
  have lnf : (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧⟦"newFreePtr" ↦ p + 96⟧)["newFreePtr"]!!
      = p + 96 := lookup_insert' hok2
  rw [lnf, hgt]
  have hok4 : isOk (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧) :=
    isOk_insert.mpr hok3
  have l3nf : (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧)["newFreePtr"]!!
      = p + 96 := by
    rw [lookup_insert_of_ne (by decide)]; exact lnf
  have l3mem : (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧)["memPtr"]!!
      = p := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]; exact l_mem2
  rw [l3nf, l3mem, hlt]
  have l4a : (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)["split_expr_3"]!!
      = 0 := by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_insert' hok3
  have l4b : (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)["split_expr_4"]!!
      = 0 := lookup_insert' hok4
  rw [l4a, l4b]
  rw [show Fin.lor (0 : UInt256) 0 = (0 : UInt256) from by decide]
  simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  have hok5 : isOk (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧) :=
    isOk_insert.mpr hok4
  have l5nf : (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)["newFreePtr"]!!
      = p + 96 := by
    rw [lookup_insert_of_ne (by decide)]; exact l3nf
  rw [l5nf]
  have hBevm : B.evm = evm := by
    rw [hB]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  simp only [evm_insert, evm_Ok]
  rw [hBevm]
  have hin_ok : isOk ((B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)🇪⟦evm.mstore 64 (p + 96)⟧) := by
    rw [isOk_setEvm]; exact hok5
  rw [reviveJump_of_isOk hin_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = evm.mstore 64 (p + 96) := by
    have h := congrArg State.evm hi
    rw [evm_setEvm_of_isOk hok5] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]
  rfl

/-! ### The six prelude helpers -/

/-- `write_to_memory_uint16(p, x)`: one masked `mstore`. -/
lemma write16_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {p x : Literal} :
    execCall (fuel+1) write_to_memory_uint16 [] (Ok evm store, [p, x])
      = (Ok evm store).setEvm (evm.mstore p (Fin.land x 65535)) := by
  unfold execCall call write_to_memory_uint16
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMAnd', EVMMstore']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["memPtr", "value"], [p, x]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["memPtr", "value"], [p, x]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hx : ((Ok evm store)☎️⟦["memPtr", "value"], [p, x]⟧)["value"]!! = x :=
    lookup_initcall_2 (by decide)
  rw [hx]
  have hok1 : isOk ((Ok evm store)☎️⟦["memPtr", "value"], [p, x]⟧⟦"split_expr_0" ↦ Fin.land x 65535⟧) :=
    isOk_insert.mpr hok0
  have hp1 : ((Ok evm store)☎️⟦["memPtr", "value"], [p, x]⟧⟦"split_expr_0" ↦ Fin.land x 65535⟧)["memPtr"]!!
      = p := by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_initcall_1
  have hs1 : ((Ok evm store)☎️⟦["memPtr", "value"], [p, x]⟧⟦"split_expr_0" ↦ Fin.land x 65535⟧)["split_expr_0"]!!
      = Fin.land x 65535 := lookup_insert' hok0
  rw [hp1, hs1]
  simp only [evm_insert]
  rw [hevm0]
  have hin_ok : isOk (((Ok evm store)☎️⟦["memPtr", "value"], [p, x]⟧⟦"split_expr_0" ↦ Fin.land x 65535⟧)🇪⟦evm.mstore p (Fin.land x 65535)⟧) := by
    rw [isOk_setEvm]; exact hok1
  rw [reviveJump_of_isOk hin_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = evm.mstore p (Fin.land x 65535) := by
    have h := congrArg State.evm hi
    rw [evm_setEvm_of_isOk hok1] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]
  rfl

/-- `write_to_memory_address(p, x)`: one address-masked `mstore`. -/
lemma writeaddr_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {p x : Literal} :
    execCall (fuel+1) write_to_memory_address [] (Ok evm store, [p, x])
      = (Ok evm store).setEvm
          (evm.mstore p (Fin.land x (Fin.shiftLeft 1 160 - 1))) := by
  unfold execCall call write_to_memory_address
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMShl', EVMSub', EVMAnd', EVMMstore']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["memPtr", "value"], [p, x]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["memPtr", "value"], [p, x]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  set B := (Ok evm store)☎️⟦["memPtr", "value"], [p, x]⟧ with hB
  have hok1 : isOk (B⟦"split_expr_0" ↦ Fin.shiftLeft 1 160⟧) := isOk_insert.mpr hok0
  have l0 : (B⟦"split_expr_0" ↦ Fin.shiftLeft 1 160⟧)["split_expr_0"]!!
      = Fin.shiftLeft 1 160 := lookup_insert' hok0
  rw [l0]
  have hok2 : isOk (B⟦"split_expr_0" ↦ Fin.shiftLeft 1 160⟧⟦"split_expr_1" ↦ Fin.shiftLeft 1 160 - 1⟧) :=
    isOk_insert.mpr hok1
  have l1a : (B⟦"split_expr_0" ↦ Fin.shiftLeft 1 160⟧⟦"split_expr_1" ↦ Fin.shiftLeft 1 160 - 1⟧)["value"]!!
      = x := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide), hB]
    exact lookup_initcall_2 (by decide)
  have l1b : (B⟦"split_expr_0" ↦ Fin.shiftLeft 1 160⟧⟦"split_expr_1" ↦ Fin.shiftLeft 1 160 - 1⟧)["split_expr_1"]!!
      = Fin.shiftLeft 1 160 - 1 := lookup_insert' hok1
  rw [l1a, l1b]
  have hok3 : isOk (B⟦"split_expr_0" ↦ Fin.shiftLeft 1 160⟧⟦"split_expr_1" ↦ Fin.shiftLeft 1 160 - 1⟧⟦"split_expr_2" ↦ Fin.land x (Fin.shiftLeft 1 160 - 1)⟧) :=
    isOk_insert.mpr hok2
  have l2a : (B⟦"split_expr_0" ↦ Fin.shiftLeft 1 160⟧⟦"split_expr_1" ↦ Fin.shiftLeft 1 160 - 1⟧⟦"split_expr_2" ↦ Fin.land x (Fin.shiftLeft 1 160 - 1)⟧)["memPtr"]!!
      = p := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
        lookup_insert_of_ne (by decide), hB]
    exact lookup_initcall_1
  have l2b : (B⟦"split_expr_0" ↦ Fin.shiftLeft 1 160⟧⟦"split_expr_1" ↦ Fin.shiftLeft 1 160 - 1⟧⟦"split_expr_2" ↦ Fin.land x (Fin.shiftLeft 1 160 - 1)⟧)["split_expr_2"]!!
      = Fin.land x (Fin.shiftLeft 1 160 - 1) := lookup_insert' hok2
  rw [l2a, l2b]
  simp only [evm_insert]
  rw [hB] at hevm0 ⊢
  rw [hevm0]
  have hin_ok : isOk (((Ok evm store)☎️⟦["memPtr", "value"], [p, x]⟧⟦"split_expr_0" ↦ Fin.shiftLeft 1 160⟧⟦"split_expr_1" ↦ Fin.shiftLeft 1 160 - 1⟧⟦"split_expr_2" ↦ Fin.land x (Fin.shiftLeft 1 160 - 1)⟧)🇪⟦evm.mstore p (Fin.land x (Fin.shiftLeft 1 160 - 1))⟧) := by
    rw [isOk_setEvm, isOk_insert, isOk_insert, isOk_insert]; exact hok0
  rw [reviveJump_of_isOk hin_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = evm.mstore p (Fin.land x (Fin.shiftLeft 1 160 - 1)) := by
    have h := congrArg State.evm hi
    rw [evm_setEvm_of_isOk (by rw [isOk_insert, isOk_insert, isOk_insert]; exact hok0)] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]
  rfl

/-- `allocate_memory_7476()`: bump the free pointer by 96, return the old one. -/
lemma alloc96_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {v : Identifier}
    (hp : (evm.mload 64).val + 96 ≤ 18446744073709551615) :
    execCall (fuel+1) allocate_memory_7476 [v] (Ok evm store, [])
      = Ok (evm.mstore 64 (evm.mload 64 + 96)) (store.insert v (evm.mload 64)) := by
  unfold execCall call allocate_memory_7476
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall', ExprStmtCall', LetCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMload']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦[], []⟧) := isOk_initcall_of_isOk trivial
  obtain ⟨e0, σ0, h0⟩ := State_of_isOk hok0
  have he0 : e0 = evm := by
    have hx := congrArg State.evm h0
    rw [show ((Ok evm store)☎️⟦[], []⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at hx
    exact hx.symm
  simp only [h0, he0]
  simp only [insert_Ok, evm_Ok]
  have l0 : (Ok evm (Finmap.insert "memPtr" (evm.mload 64) σ0))["memPtr"]!!
      = evm.mload 64 := lookup_insert_self_fin
  rw [l0]
  rw [finalize_allocation_96'_call hp]
  rw [setEvm_Ok]
  have l1 : (Ok (evm.mstore 64 (evm.mload 64 + 96))
      (Finmap.insert "memPtr" (evm.mload 64) σ0))["memPtr"]!! = evm.mload 64 :=
    lookup_insert_self_fin
  rw [l1]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [multifill_cons, multifill_nil, insert_Ok]

/-- `abi_encode_bytes32(h, x)`: one `mstore`, returns `h + 32`. -/
lemma abienc32_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {h x : Literal} {t : Identifier} :
    execCall (fuel+1) abi_encode_bytes32 [t] (Ok evm store, [h, x])
      = Ok (evm.mstore h x) (store.insert t (h + 32)) := by
  unfold execCall call abi_encode_bytes32
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, nil]
  simp only [Assign', LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMAdd', EVMMstore']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["headStart", "value0"], [h, x]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["headStart", "value0"], [h, x]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hh : ((Ok evm store)☎️⟦["headStart", "value0"], [h, x]⟧)["headStart"]!! = h :=
    lookup_initcall_1
  rw [hh]
  have hok1 : isOk ((Ok evm store)☎️⟦["headStart", "value0"], [h, x]⟧⟦"tail" ↦ h + 32⟧) :=
    isOk_insert.mpr hok0
  have l1a : ((Ok evm store)☎️⟦["headStart", "value0"], [h, x]⟧⟦"tail" ↦ h + 32⟧)["headStart"]!!
      = h := by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_initcall_1
  have l1b : ((Ok evm store)☎️⟦["headStart", "value0"], [h, x]⟧⟦"tail" ↦ h + 32⟧)["value0"]!!
      = x := by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_initcall_2 (by decide)
  rw [l1a, l1b]
  simp only [evm_insert]
  rw [hevm0]
  have hin_ok : isOk ((((Ok evm store)☎️⟦["headStart", "value0"], [h, x]⟧⟦"tail" ↦ h + 32⟧)).setEvm (evm.mstore h x)) := by
    rw [isOk_setEvm]; exact hok1
  have ltail : ((((Ok evm store)☎️⟦["headStart", "value0"], [h, x]⟧⟦"tail" ↦ h + 32⟧)).setEvm (evm.mstore h x))["tail"]!!
      = h + 32 := by
    rw [lookup_setEvm_of_isOk hok1]
    exact lookup_insert' hok0
  rw [ltail]
  rw [reviveJump_of_isOk hin_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = evm.mstore h x := by
    have hq := congrArg State.evm hi
    rw [evm_setEvm_of_isOk hok1] at hq
    exact hq.symm
  rw [hi, setStore_ok]
  simp only [insert_Ok]
  rw [hi_evm]

/-- The pinned commitment-tree sender: the constant `0x10012 = 65554`. -/
lemma constaddr_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {v : Identifier} :
    execCall (fuel+1) constant_L2_INTEROP_COMMITMENT_TREE_ADDR [v] (Ok evm store, [])
      = Ok evm (store.insert v 65554) := by
  unfold execCall call constant_L2_INTEROP_COMMITMENT_TREE_ADDR
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, cons, cons, nil]
  simp only [Assign', LetEq', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append]
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦[], []⟧) := isOk_initcall_of_isOk trivial
  obtain ⟨e0, σ0, h0⟩ := State_of_isOk hok0
  have he0 : e0 = evm := by
    have hx := congrArg State.evm h0
    rw [show ((Ok evm store)☎️⟦[], []⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at hx
    exact hx.symm
  simp only [h0, he0, insert_Ok]
  have lsum : (Ok evm (Finmap.insert "_1" 0 (Finmap.insert "_1" 0
      (Finmap.insert "sum" 65554 (Finmap.insert "sum" 0 σ0)))))["sum"]!! = 65554 := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  rw [lsum]
  have lret : (Ok evm (Finmap.insert "ret" 65554
      (Finmap.insert "_1" 0 (Finmap.insert "_1" 0
        (Finmap.insert "sum" 65554 (Finmap.insert "sum" 0 σ0))))))["ret"]!!
      = 65554 := lookup_insert_self_fin
  rw [lret]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [multifill_cons, multifill_nil, insert_Ok]

/-- `cleanup_address(x)`: pure address masking. -/
lemma cleanupaddr_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x : Literal} {v : Identifier} :
    execCall (fuel+1) cleanup_address [v] (Ok evm store, [x])
      = Ok evm (store.insert v (Fin.land x (Fin.shiftLeft 1 160 - 1))) := by
  unfold execCall call cleanup_address
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, nil]
  simp only [Assign', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMShl', EVMSub', EVMAnd']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["value"], [x]⟧) := isOk_initcall_of_isOk trivial
  obtain ⟨e0, σ0, h0⟩ := State_of_isOk hok0
  have he0 : e0 = evm := by
    have hx := congrArg State.evm h0
    rw [show ((Ok evm store)☎️⟦["value"], [x]⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at hx
    exact hx.symm
  have hxl : ((Ok evm store)☎️⟦["value"], [x]⟧)["value"]!! = x := lookup_initcall_1
  rw [h0, he0] at hxl
  simp only [h0, he0, insert_Ok]
  have l0 : (Ok evm (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 160) σ0))["split_expr_0"]!!
      = Fin.shiftLeft 1 160 := lookup_insert_self_fin
  rw [l0]
  have l1a : (Ok evm (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 160 - 1)
      (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 160) σ0)))["value"]!! = x := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact hxl
  have l1b : (Ok evm (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 160 - 1)
      (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 160) σ0)))["split_expr_1"]!!
      = Fin.shiftLeft 1 160 - 1 := lookup_insert_self_fin
  rw [l1a, l1b]
  have lc : (Ok evm (Finmap.insert "cleaned" (Fin.land x (Fin.shiftLeft 1 160 - 1))
      (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 160 - 1)
        (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 160) σ0))))["cleaned"]!!
      = Fin.land x (Fin.shiftLeft 1 160 - 1) := lookup_insert_self_fin
  rw [lc]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [multifill_cons, multifill_nil, insert_Ok]

end

end generated.AtomicFlowManager.AtomicFlowManager
