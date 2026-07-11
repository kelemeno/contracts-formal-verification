import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7182708311549001418
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_8692170500034331446
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11

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

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
