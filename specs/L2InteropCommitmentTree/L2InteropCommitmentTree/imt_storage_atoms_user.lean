import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7182708311549001418
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_8692170500034331446
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mod_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256

import specs.KeccakDeterminism

/-
  STORAGE ATOMS for the IMT tree-builder (`fun_updateLeaf` / `fun_pushNewLeaf`).

  The concrete insert path reads siblings from and writes nodes to the
  2-level dynamic storage arrays of `L2InteropCommitmentTree`.  This file
  gives closed forms for its three storage helpers (success paths):

  * `storage_array_index_call` — the array element accessor: bounds-checked,
    returns `(keccak(arraySlot) + index, 0)`; evm effect = one scratch write +
    the keccak step (`arrOut`, the 32-byte analog of `accOut`).
  * `extract_call_0` — the byte-offset extractor at offset 0 is the identity.
  * `update_storage_call_0` — the masked store at offset 0 is a plain
    `sstore slot value` (the mask degenerates to a full overwrite).

  These are the U1 atoms of the tree-builder arc (the remaining obligation of
  the delivered-XOR-reclaimed capstone).  Axiom-free.
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

/-- Fin shifts by zero are the identity. -/
private lemma shiftLeft_zero (x : UInt256) : Fin.shiftLeft x 0 = x := by
  apply Fin.ext
  have hv : (Fin.shiftLeft x 0).val = (x.val <<< ((0 : UInt256)).val) % UInt256.size := rfl
  rw [hv, show ((0 : UInt256)).val = 0 from by decide, Nat.shiftLeft_zero,
      Nat.mod_eq_of_lt x.isLt]

private lemma shiftRight_zero (x : UInt256) : Fin.shiftRight x 0 = x := by
  apply Fin.ext
  have hv : (Fin.shiftRight x 0).val = x.val >>> ((0 : UInt256)).val % UInt256.size := rfl
  rw [hv, show ((0 : UInt256)).val = 0 from by decide]
  simp [Nat.mod_eq_of_lt x.isLt]

private lemma land_zero (x : UInt256) : Fin.land x 0 = 0 := by
  apply Fin.ext
  have hv : (Fin.land x 0).val = (Nat.land x.val ((0 : UInt256)).val) % UInt256.size := rfl
  rw [hv, show ((0 : UInt256)).val = 0 from by decide,
      show Nat.land (x.val) 0 = x.val &&& 0 from rfl, Nat.and_zero, Nat.zero_mod]

private lemma lor_zero_left (x : UInt256) : Fin.lor 0 x = x := by
  apply Fin.ext
  have hv : (Fin.lor 0 x).val = (Nat.lor ((0 : UInt256)).val x.val) % UInt256.size := rfl
  rw [hv, show ((0 : UInt256)).val = 0 from by decide,
      show Nat.lor 0 (x.val) = 0 ||| x.val from rfl, Nat.zero_or,
      Nat.mod_eq_of_lt x.isLt]

/-- The array-slot hash step: `keccak256` of the array slot written at scratch
`[0, 32)` — the 32-byte analog of `accOut`. -/
def arrOut (σ : EVMState) (a : UInt256) : UInt256 × EVMState :=
  keccakOut (σ.mstore 0 a) 0 32

/-- **Closed form of `extract_from_storage_value_dynamict_bytes32(x, 0)`**:
at byte offset 0 the extractor is the identity. -/
lemma extract_call_0
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x : Literal} {v : Identifier} :
    execCall (fuel+1) extract_from_storage_value_dynamict_bytes32 [v]
        (Ok evm store, [x, 0])
      = Ok evm (store.insert v x) := by
  unfold execCall call extract_from_storage_value_dynamict_bytes32
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, nil]
  simp only [LetPrimCall', AssignPrimCall', evalArgs, evalTail, cons', head',
             reverse', multifill', PrimCall', Lit', Var', execPrimCall,
             evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMShl', EVMShr']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["slot_value", "offset"], [x, 0]⟧) :=
    isOk_initcall_of_isOk trivial
  have hoff : ((Ok evm store)☎️⟦["slot_value", "offset"], [x, 0]⟧)["offset"]!! = 0 :=
    lookup_initcall_2 (by decide)
  rw [hoff]
  rw [show Fin.shiftLeft (0 : UInt256) 3 = (0 : UInt256) from by decide]
  have hsv : ((Ok evm store)☎️⟦["slot_value", "offset"], [x, 0]⟧⟦"split_expr_0" ↦ 0⟧)["slot_value"]!!
      = x := by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_initcall_1
  have hs0 : ((Ok evm store)☎️⟦["slot_value", "offset"], [x, 0]⟧⟦"split_expr_0" ↦ 0⟧)["split_expr_0"]!!
      = 0 := lookup_insert' hok0
  rw [hsv, hs0, shiftRight_zero]
  have hok2 : isOk ((Ok evm store)☎️⟦["slot_value", "offset"], [x, 0]⟧⟦"split_expr_0" ↦ 0⟧⟦"value" ↦ x⟧) := by
    rw [isOk_insert, isOk_insert]; exact hok0
  rw [reviveJump_of_isOk hok2]
  simp only [overwrite?_of_Ok]
  rw [lookup_insert' (by rw [isOk_insert]; exact hok0)]
  have hevm0 : ((Ok evm store)☎️⟦["slot_value", "offset"], [x, 0]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  obtain ⟨e2, σ2, h2⟩ := State_of_isOk hok2
  have he2 : e2 = evm := by
    have h := congrArg State.evm h2
    rw [evm_insert, evm_insert, hevm0] at h
    exact h.symm
  rw [h2, setStore_ok, he2]
  simp only [multifill_cons, multifill_nil, insert_Ok]

private lemma setEvm_Ok {e e' : EVMState} {σ : VarStore} :
    (Ok e σ).setEvm e' = Ok e' σ := rfl

/-- Chunk 1 of the masked update: the mask computation degenerates at offset 0. -/
private lemma mask_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {slot : Literal}
    (hslot : (Ok evm σ)["slot"]!! = slot)
    (hoff : (Ok evm σ)["offset"]!! = 0) :
    exec (fuel+1) (.Block
        [LetPrimCall ["_1"] .Sload [Var "slot"],
         LetPrimCall ["shiftBits"] .Shl [Lit 3, Var "offset"],
         LetPrimCall ["split_expr_0"] .Not [Lit 0],
         LetPrimCall ["split_expr_1"] .Shl [Var "shiftBits", Var "split_expr_0"],
         LetPrimCall ["split_expr_2"] .Not [Var "split_expr_1"]]) (Ok evm σ)
      = Ok evm (Finmap.insert "split_expr_2" 0
          (Finmap.insert "split_expr_1" (UInt256.lnot 0)
            (Finmap.insert "split_expr_0" (UInt256.lnot 0)
              (Finmap.insert "shiftBits" 0
                (Finmap.insert "_1" (evm.sload slot) σ))))) := by
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [hslot]
  simp only [evm_Ok, insert_Ok]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMShl', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hoff]
  rw [show Fin.shiftLeft (0 : UInt256) 3 = (0 : UInt256) from by decide]
  simp only [insert_Ok]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMNot', multifill_cons, multifill_nil, insert_Ok]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMShl', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [shiftLeft_zero]
  simp only [insert_Ok]
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMNot', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [show UInt256.lnot (UInt256.lnot 0) = (0 : UInt256) from by decide]
  simp only [insert_Ok]

/-- Chunk 2: masked combine + store — a full overwrite at offset 0. -/
private lemma store_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {slot value : Literal}
    (hsb : (Ok evm σ)["shiftBits"]!! = 0)
    (h2 : (Ok evm σ)["split_expr_2"]!! = 0)
    (hval : (Ok evm σ)["value"]!! = value)
    (hslot : (Ok evm σ)["slot"]!! = slot) :
    exec (fuel+1) (.Block
        [LetPrimCall ["split_expr_3"] .And [Var "_1", Var "split_expr_2"],
         LetPrimCall ["split_expr_4"] .Shl [Var "shiftBits", Var "value"],
         LetPrimCall ["split_expr_5"] .Or [Var "split_expr_3", Var "split_expr_4"],
         ExprStmtPrimCall .Sstore [Var "slot", Var "split_expr_5"]]) (Ok evm σ)
      = Ok (evm.sstore slot value)
          (Finmap.insert "split_expr_5" value
            (Finmap.insert "split_expr_4" value
              (Finmap.insert "split_expr_3" 0 σ))) := by
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMAnd', multifill_cons, multifill_nil]
  rw [h2, land_zero]
  simp only [insert_Ok]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMShl', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hval]
  rw [lookup_insert_ne_fin (by decide), hsb]
  rw [shiftLeft_zero]
  simp only [insert_Ok]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMOr', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [lor_zero_left]
  simp only [insert_Ok]
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSstore', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hslot]
  simp only [evm_Ok, setEvm_Ok]

/-- **Closed form of `update_storage_value_bytes32_to_bytes32(slot, 0, value)`**:
at byte offset 0 the masked update is a full overwrite — `sstore slot value`. -/
lemma update_storage_call_0
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slot value : Literal} :
    execCall (fuel+1) update_storage_value_bytes32_to_bytes32 []
        (Ok evm store, [slot, 0, value])
      = Ok (evm.sstore slot value) store := by
  unfold execCall call update_storage_value_bytes32_to_bytes32
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, nil]
  set s0 := (Ok evm store)☎️⟦["slot", "offset", "value"], [slot, 0, value]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["slot"]!! = slot := by rw [hs0]; exact lookup_initcall_1
  have hp2 : s0["offset"]!! = 0 := by rw [hs0]; exact lookup_initcall_2 (by decide)
  have hp3 : s0["value"]!! = value := by
    rw [hs0]; exact lookup_initcall_3 (by decide) (by decide)
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq] at hp1 hp2 hp3 ⊢
  rw [mask_block hp1 hp2]
  rw [store_block (value := value) (slot := slot)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_self_fin])
    (by rw [lookup_insert_self_fin])
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hp3)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact hp1)]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [multifill_nil]

/-- **Closed form of `storage_array_index_access_bytes32_dyn__dyn(array, index)`**
(success path, `index < sload(array)`): returns the element slot
`keccak(array) + index` and byte offset `0`; the evm advances by the scratch
write + keccak step (`arrOut`). -/
lemma storage_array_index_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {arr idx : Literal}
    {sv ov : Identifier}
    (hlt : idx < evm.sload arr) :
    execCall (fuel+1) storage_array_index_access_bytes32_dyn__dyn [sv, ov]
        (Ok evm store, [arr, idx])
      = Ok (arrOut evm arr).2
          (Finmap.insert sv ((arrOut evm arr).1 + idx) (Finmap.insert ov 0 store)) := by
  unfold execCall call storage_array_index_access_bytes32_dyn__dyn
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
  have hp1e : ∀ e : EVMState, (Ok e σ0)["array"]!! = arr := fun _ => hp1
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
  rw [primCall_keccakOut]
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

/-- Closed form of `mod_uint256(x)`: pure, returns `x & 1` (parity). -/
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
  rw [reviveJump_of_isOk hin_ok]
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
  rw [reviveJump_of_isOk hin_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = evm := by
    have h := congrArg State.evm hi
    simp only [evm_insert] at h
    rw [show ((Ok evm store)☎️⟦["x"], [x]⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]

/-- Closed form of `checked_add_uint256(x)` (no-overflow case): `x + 1`. -/
lemma checked_add_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x : Literal} {v : Identifier}
    (hx : x.val + 1 < 2 ^ 256) :
    execCall (fuel+1) checked_add_uint256 [v] (Ok evm store, [x])
      = (Ok evm store)⟦v ↦ x + 1⟧ := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have hsucc : (x + 1).val = x.val + 1 := by
    rw [Fin.val_add, show ((1 : UInt256)).val = 1 from by decide]
    exact Nat.mod_eq_of_lt (by omega)
  have hngt : ¬ (x > x + 1) := by
    intro h
    have : (x + 1).val < x.val := h
    omega
  unfold execCall call checked_add_uint256
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, nil]
  simp only [LetEq', Assign', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMAdd']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["x"], [x]⟧) := isOk_initcall_of_isOk trivial
  rw [lookup_initcall_1]
  -- the overflow guard is skipped
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMGt']
  have hxs : ((Ok evm store)☎️⟦["x"], [x]⟧⟦"sum" ↦ x + 1⟧)["x"]!! = x := by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_initcall_1
  have hsum : ((Ok evm store)☎️⟦["x"], [x]⟧⟦"sum" ↦ x + 1⟧)["sum"]!! = x + 1 :=
    lookup_insert' hok0
  rw [hxs, hsum]
  rw [show fromBool (x > x + 1) = (0 : UInt256) from by rw [decide_eq_false hngt]; rfl]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- rets + call wrapper
  have hok2 : isOk ((Ok evm store)☎️⟦["x"], [x]⟧⟦"sum" ↦ x + 1⟧) := by
    rw [isOk_insert]; exact hok0
  rw [hsum]
  rw [reviveJump_of_isOk hok2]
  try simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hok2
  have hi_evm : ei = evm := by
    have h := congrArg State.evm hi
    simp only [evm_insert] at h
    rw [show ((Ok evm store)☎️⟦["x"], [x]⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]
  try simp only [multifill_cons, multifill_nil]

/-- Closed form of `checked_sub_uint256(x)` (`x ≠ 0`): `x - 1`. -/
lemma checked_sub_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x : Literal} {v : Identifier}
    (hx : x ≠ 0) :
    execCall (fuel+1) checked_sub_uint256 [v] (Ok evm store, [x])
      = Ok evm (Finmap.insert v (x - 1) store) := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have hxpos : 0 < x.val := by
    rcases Nat.eq_zero_or_pos x.val with h0 | h
    · exact absurd (Fin.ext (by rw [h0]; rfl) : x = 0) hx
    · exact h
  have hM : ((115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256)).val = 2 ^ 256 - 1 := by decide
  have hsub : (x + (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256)).val = x.val - 1 := by
    rw [Fin.val_add, hM]
    rw [show x.val + (2 ^ 256 - 1) = (x.val - 1) + 2 ^ 256 from by omega]
    rw [show (2 : ℕ) ^ 256 = UInt256.size from by norm_num]
    rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  have hsub1 : x + (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256) = x - 1 := by
    apply Fin.ext
    rw [hsub]
    have hv : (x - 1).val = (x.val + (UInt256.size - ((1 : UInt256)).val)) % UInt256.size := rfl
    rw [hv, show ((1 : UInt256)).val = 1 from by decide]
    rw [show x.val + (UInt256.size - 1) = (x.val - 1) + UInt256.size from by omega]
    rw [Nat.add_mod_right]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have hngt : ¬ (x + (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256) > x) := by
    intro h
    have hlt : x.val < (x + (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256)).val := h
    omega
  unfold execCall call checked_sub_uint256
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  set s0 := (Ok evm store)☎️⟦["x"], [x]⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hp1 : s0["x"]!! = x := by rw [hs0]; exact lookup_initcall_1
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq] at hp1 ⊢
  -- statement 1: split_expr_0 := not(0)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMNot', multifill_cons, multifill_nil, insert_Ok]
  rw [show (UInt256.lnot 0 : UInt256) = (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256) from by decide]
  -- statement 2: diff := add(x, split_expr_0)
  rw [cons, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMAdd', multifill_cons, multifill_nil]
  rw [lookup_insert_ne_fin (by decide), hp1, lookup_insert_self_fin]
  rw [hsub1]
  simp only [insert_Ok]
  -- statement 3: the underflow guard is skipped
  rw [cons, nil, If']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append, EVMGt']
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hp1]
  rw [show fromBool (x - 1 > x) = (0 : UInt256) from by
    rw [decide_eq_false (by rw [← hsub1]; exact hngt)]; rfl]
  try simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  try simp only [overwrite?_of_Ok]
  -- rets + call wrapper
  rw [lookup_insert_self_fin]
  rw [reviveJump_of_isOk (by trivial)]
  try simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  try simp only [multifill_cons, multifill_nil, insert_Ok]

/-- The 2-level storage-array sibling read: element `j` of the level-`lvl`
array inside the array-of-arrays at `base`.  Value + resulting evm (two
keccak steps). -/
def sibRead (σ : EVMState) (base lvl j : UInt256) : UInt256 × EVMState :=
  ((arrOut (arrOut σ base).2 ((arrOut σ base).1 + lvl)).2.sload
      ((arrOut (arrOut σ base).2 ((arrOut σ base).1 + lvl)).1 + j),
   (arrOut (arrOut σ base).2 ((arrOut σ base).1 + lvl)).2)

/-- **Closed form of the odd-branch sibling read** (`updateLeaf` loop, case
`index & 1 = 1`): reads element `index − 1` of the level-`lvl` node array —
the left sibling — into `split_expr_9`. -/
lemma oddRead_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {base lvl idx : Literal}
    (h1 : (Ok evm σ)["_1"]!! = base)
    (hlvl : (Ok evm σ)["var_i"]!! = lvl)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hidx0 : idx ≠ 0)
    (hb1 : lvl < evm.sload base)
    (hb2 : idx - 1 < (arrOut evm base).2.sload ((arrOut evm base).1 + lvl)) :
    exec (fuel+1) (.Block
        [LetCall ["_6", "_7"] storage_array_index_access_bytes32_dyn__dyn
           [Var "_1", Var "var_i"],
         LetCall ["split_expr_7"] checked_sub_uint256 [Var "var_index"],
         LetCall ["_8", "_9"] storage_array_index_access_bytes32_dyn__dyn
           [Var "_6", Var "split_expr_7"],
         LetPrimCall ["split_expr_8"] .Sload [Var "_8"],
         LetCall ["split_expr_9"] extract_from_storage_value_dynamict_bytes32
           [Var "split_expr_8", Var "_9"]]) (Ok evm σ)
      = Ok (sibRead evm base lvl (idx - 1)).2
          (Finmap.insert "split_expr_9" (sibRead evm base lvl (idx - 1)).1
            (Finmap.insert "split_expr_8" (sibRead evm base lvl (idx - 1)).1
              (Finmap.insert "_8"
                ((arrOut (arrOut evm base).2 ((arrOut evm base).1 + lvl)).1 + (idx - 1))
                (Finmap.insert "_9" 0
                  (Finmap.insert "split_expr_7" (idx - 1)
                    (Finmap.insert "_6" ((arrOut evm base).1 + lvl)
                      (Finmap.insert "_7" 0 σ))))))) := by
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  -- statement 1: _6, _7 := arrayaccess(_1, var_i)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [h1, hlvl]
  rw [storage_array_index_call hb1]
  -- statement 2: split_expr_7 := checked_sub(var_index)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hidxe]
  rw [checked_sub_call hidx0]
  -- statement 3: _8, _9 := arrayaccess(_6, split_expr_7)
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [lookup_insert_self_fin]
  rw [storage_array_index_call hb2]
  -- statement 4: split_expr_8 := sload(_8)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             EVMSload', multifill_cons, multifill_nil]
  rw [lookup_insert_self_fin]
  simp only [evm_Ok, insert_Ok]
  -- statement 5: split_expr_9 := extract(split_expr_8, _9)
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

/-- **Closed form of the even-branch sibling read** (`updateLeaf` loop, case
`index & 1 = 0`, non-edge): reads element `index + 1` of the level-`lvl` node
array — the right sibling — into `expr`. -/
lemma evenRead_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {base lvl idx : Literal}
    (h1 : (Ok evm σ)["_1"]!! = base)
    (hlvl : (Ok evm σ)["var_i"]!! = lvl)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hadd : idx.val + 1 < 2 ^ 256)
    (hb1 : lvl < evm.sload base)
    (hb2 : idx + 1 < (arrOut evm base).2.sload ((arrOut evm base).1 + lvl)) :
    exec (fuel+1) (.Block
        [LetCall ["_10", "_11"] storage_array_index_access_bytes32_dyn__dyn
           [Var "_1", Var "var_i"],
         LetCall ["split_expr_10"] checked_add_uint256 [Var "var_index"],
         LetCall ["_12", "_13"] storage_array_index_access_bytes32_dyn__dyn
           [Var "_10", Var "split_expr_10"],
         LetPrimCall ["split_expr_11"] .Sload [Var "_12"],
         AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
           [Var "split_expr_11", Var "_13"]]) (Ok evm σ)
      = Ok (sibRead evm base lvl (idx + 1)).2
          (Finmap.insert "expr" (sibRead evm base lvl (idx + 1)).1
            (Finmap.insert "split_expr_11" (sibRead evm base lvl (idx + 1)).1
              (Finmap.insert "_12"
                ((arrOut (arrOut evm base).2 ((arrOut evm base).1 + lvl)).1 + (idx + 1))
                (Finmap.insert "_13" 0
                  (Finmap.insert "split_expr_10" (idx + 1)
                    (Finmap.insert "_10" ((arrOut evm base).1 + lvl)
                      (Finmap.insert "_11" 0 σ))))))) := by
  have hidxe : ∀ e : EVMState, (Ok e σ)["var_index"]!! = idx := fun _ => hidx
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [h1, hlvl]
  rw [storage_array_index_call hb1]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hidxe]
  rw [checked_add_call hadd]
  rw [show ((Ok (arrOut evm base).2
      (Finmap.insert "_10" ((arrOut evm base).1 + lvl) (Finmap.insert "_11" 0 σ)) : State)⟦"split_expr_10" ↦ idx + 1⟧)
      = Ok (arrOut evm base).2 (Finmap.insert "split_expr_10" (idx + 1)
          (Finmap.insert "_10" ((arrOut evm base).1 + lvl) (Finmap.insert "_11" 0 σ))) from rfl]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [lookup_insert_self_fin]
  rw [storage_array_index_call hb2]
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

/-- One-level storage-array read (the roots side-array at `selfSlot + 3`). -/
def sideRead (σ : EVMState) (slot lvl : UInt256) : UInt256 × EVMState :=
  ((arrOut σ slot).2.sload ((arrOut σ slot).1 + lvl), (arrOut σ slot).2)

/-- **Closed form of the edge-branch read** (`updateLeaf` loop, even case at
the tree edge): reads element `lvl` of the side array at `selfSlot + 3` into
`expr` (the duplicated-node convention). -/
lemma edgeRead_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {selfSlot lvl : Literal}
    (hss : (Ok evm σ)["var_self_slot"]!! = selfSlot)
    (hlvl : (Ok evm σ)["var_i"]!! = lvl)
    (hb : lvl < evm.sload (selfSlot + 3)) :
    exec (fuel+1) (.Block
        [LetPrimCall ["split_expr_12"] .Add [Var "var_self_slot", Lit 3],
         LetCall ["_14", "_15"] storage_array_index_access_bytes32_dyn__dyn
           [Var "split_expr_12", Var "var_i"],
         LetPrimCall ["split_expr_13"] .Sload [Var "_14"],
         AssignCall ["expr"] extract_from_storage_value_dynamict_bytes32
           [Var "split_expr_13", Var "_15"]]) (Ok evm σ)
      = Ok (sideRead evm (selfSlot + 3) lvl).2
          (Finmap.insert "expr" (sideRead evm (selfSlot + 3) lvl).1
            (Finmap.insert "split_expr_13" (sideRead evm (selfSlot + 3) lvl).1
              (Finmap.insert "_14" ((arrOut evm (selfSlot + 3)).1 + lvl)
                (Finmap.insert "_15" 0
                  (Finmap.insert "split_expr_12" (selfSlot + 3) σ))))) := by
  have hlvle : ∀ e : EVMState, (Ok e σ)["var_i"]!! = lvl := fun _ => hlvl
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
  rw [lookup_insert_ne_fin (by decide), hlvle]
  rw [storage_array_index_call hb]
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

/-- **Closed form of the div/store prep block**: halves `var_index` and
`var_maxNodeNumber`, and computes the parent-node write slot — element
`index >> 1` of the level-`lvl+1` array. -/
lemma divStore_prep_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {base lvl idx maxN : Literal}
    (h1 : (Ok evm σ)["_1"]!! = base)
    (hlvl : (Ok evm σ)["var_i"]!! = lvl)
    (hidx : (Ok evm σ)["var_index"]!! = idx)
    (hmax : (Ok evm σ)["var_maxNodeNumber"]!! = maxN)
    (haddl : lvl.val + 1 < 2 ^ 256)
    (hb1 : lvl + 1 < evm.sload base)
    (hb2 : Fin.shiftRight idx 1
        < (arrOut evm base).2.sload ((arrOut evm base).1 + (lvl + 1))) :
    exec (fuel+1) (.Block
        [AssignCall ["var_index"] checked_div_uint256 [Var "var_index"],
         AssignCall ["var_maxNodeNumber"] checked_div_uint256 [Var "var_maxNodeNumber"],
         LetCall ["split_expr_14"] checked_add_uint256 [Var "var_i"],
         LetCall ["_16", "_17"] storage_array_index_access_bytes32_dyn__dyn
           [Var "_1", Var "split_expr_14"],
         LetCall ["_18", "_19"] storage_array_index_access_bytes32_dyn__dyn
           [Var "_16", Var "var_index"]]) (Ok evm σ)
      = Ok (arrOut (arrOut evm base).2 ((arrOut evm base).1 + (lvl + 1))).2
          (Finmap.insert "_18"
              ((arrOut (arrOut evm base).2 ((arrOut evm base).1 + (lvl + 1))).1
                + Fin.shiftRight idx 1)
            (Finmap.insert "_19" 0
              (Finmap.insert "_16" ((arrOut evm base).1 + (lvl + 1))
                (Finmap.insert "_17" 0
                  (Finmap.insert "split_expr_14" (lvl + 1)
                    (Finmap.insert "var_maxNodeNumber" (Fin.shiftRight maxN 1)
                      (Finmap.insert "var_index" (Fin.shiftRight idx 1) σ))))))) := by
  have hmaxe : ∀ e : EVMState, (Ok e σ)["var_maxNodeNumber"]!! = maxN := fun _ => hmax
  have hlvle : ∀ e : EVMState, (Ok e σ)["var_i"]!! = lvl := fun _ => hlvl
  have h1e : ∀ e : EVMState, (Ok e σ)["_1"]!! = base := fun _ => h1
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
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), h1e]
  rw [lookup_insert_self_fin]
  rw [storage_array_index_call hb1]
  rw [cons, nil, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [storage_array_index_call hb2]

/-- **Closed form of the store step**: writes the recomputed node at the
prepared slot — a plain `sstore`. -/
lemma store_call_block
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {wslot cur : Literal}
    (h18 : (Ok evm σ)["_18"]!! = wslot)
    (h19 : (Ok evm σ)["_19"]!! = 0)
    (hcur : (Ok evm σ)["var_currentHash"]!! = cur) :
    exec (fuel+1) (.Block
        [ExprStmtCall update_storage_value_bytes32_to_bytes32
           [Var "_18", Var "_19", Var "var_currentHash"]]) (Ok evm σ)
      = Ok (evm.sstore wslot cur) σ := by
  rw [cons, nil, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall, List.reverse_cons,
             List.reverse_nil, List.nil_append, List.singleton_append,
             List.append_assoc, List.cons_append]
  rw [h18, h19, hcur]
  rw [update_storage_call_0]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
