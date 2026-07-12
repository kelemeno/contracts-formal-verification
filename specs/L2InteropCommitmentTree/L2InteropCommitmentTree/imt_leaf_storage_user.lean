import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5196
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.read_from_storage_reference_type_struct_IMTLeaf
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation_5187
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_walk_discharge_user
import specs.IMTAbstract
import specs.KeccakInjective

/-
  THE LEAVES-MAPPING STORAGE PRIMITIVES — the insert glue's alphabet.

  The dispatcher-inlined IMT insert (the (B) boundary) sequences three named,
  VC-generated helpers over the `leaves` mapping (storage slot 4):

  * `mapping_…_5196(key)`  — the slot of leaf `key`: `keccak256(key ‖ 4)`,
  * `copy_struct_to_storage(slot, ptr)` — write a leaf struct: three
    `sstore`s of `(value, nextIndex, nextValue)` at `slot`/`+1`/`+2`,
  * `read_from_storage(slot)` — the mirror-image read (future work).

  This file closes the first two: the mapping accessor is exactly one
  `accOut` step at `(key, 4)` (the same keccak-slot atom as the whole walk
  machinery), and the struct write is exactly three word `sstore`s of the
  three memory fields.  With these, the leaves-mapping abstraction
  ("`AbsLeaf` at index `i` lives at `keccak(i ‖ 4) + 0/1/2`") is definable
  against verified primitives, narrowing the (B) glue to pure sequencing.

  Axiom-free.
-/

namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-! ### Local state-plumbing helpers -/

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

private lemma lookup_setEvm_of_isOk {s : State} {e : EVMState} {k : Identifier}
    (h : isOk s) : (s.setEvm e)[k]!! = s[k]!! := by
  obtain ⟨evm₀, st, rfl⟩ := State_of_isOk h; rfl

private lemma lookup_ok_evm {σ : VarStore} {k : Identifier} (e e' : EVMState) :
    (Ok e σ)[k]!! = (Ok e' σ)[k]!! := rfl

private lemma primCall_keccakOut {s : State} {a b : Literal} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (keccakOut s.evm a b).2, [(keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

private lemma machine_state_sstore (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).machine_state = σ.machine_state := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-- `sstore` leaves every memory read unchanged. -/
private lemma mload_sstore (σ : EVMState) (a v p : UInt256) :
    (σ.sstore a v).mload p = σ.mload p := by
  show (σ.sstore a v).machine_state.lookupMemory p = σ.machine_state.lookupMemory p
  rw [machine_state_sstore]

/-! ### The leaf-slot accessor: `keccak256(key ‖ 4)` as one `accOut` step -/

/-- **Closed form of `mapping_…_5196(key)`** — the `leaves` mapping accessor
at storage slot 4: one `accOut` step at `(key, 4)`. -/
lemma mapping_leaves_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {key : Literal} {v : Identifier} :
    execCall (fuel+1) mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5196
        [v] (Ok evm store, [key])
      = Ok (accOut evm key 4).2 (store.insert v (accOut evm key 4).1) := by
  unfold execCall call mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5196
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, nil]
  simp only [ExprStmtPrimCall', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMstore']
  simp only [multifill', multifill_nil, multifill_cons, overwrite?_of_Ok]
  rw [primCall_keccakOut]
  have hok₀ : isOk ((Ok evm store)☎️⟦["key"], [key]⟧) := isOk_initcall_of_isOk trivial
  have hevm₀ : ((Ok evm store)☎️⟦["key"], [key]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hkey : ((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!! = key := lookup_initcall_1
  set host := (((Ok evm store)☎️⟦["key"], [key]⟧)
      🇪⟦((Ok evm store)☎️⟦["key"], [key]⟧).evm.mstore 0
          (((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!!)⟧)
      🇪⟦(((Ok evm store)☎️⟦["key"], [key]⟧)
          🇪⟦((Ok evm store)☎️⟦["key"], [key]⟧).evm.mstore 0
              (((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!!)⟧).evm.mstore 32 4⟧
      with hhost
  have hhost_ok : isOk host := by
    rw [hhost, isOk_setEvm, isOk_setEvm]; exact hok₀
  have hhost_evm : host.evm = (evm.mstore 0 key).mstore 32 4 := by
    rw [hhost, evm_setEvm_of_isOk (by rw [isOk_setEvm]; exact hok₀),
        evm_setEvm_of_isOk hok₀, hevm₀, hkey]
  rw [hhost_evm]
  unfold accOut
  generalize hout : keccakOut ((evm.mstore 0 key).mstore 32 4) 0 64 = out
  simp only [multifill_cons, multifill_nil]
  have hsetEvm_ok : isOk (host.setEvm out.2) := by
    rw [isOk_setEvm]; exact hhost_ok
  have hin_ok : isOk ((host.setEvm out.2)⟦"dataSlot" ↦ out.1⟧) := by
    rw [isOk_insert]; exact hsetEvm_ok
  rw [lookup_insert' hsetEvm_ok]
  rw [reviveJump_of_isOk hin_ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = out.2 := by
    have h := congrArg State.evm hi
    rw [evm_insert, evm_setEvm_of_isOk hhost_ok] at h
    exact h.symm
  rw [hi, setStore_ok]
  simp only [insert_Ok]
  rw [hi_evm]

/-! ### The leaf-struct write: three word `sstore`s -/

private def copyBlk1 : Stmt := <s
  {
    let split_expr_0 := mload(value)
    sstore(slot, split_expr_0)
    let split_expr_1 := add(slot, 1)
    let split_expr_2 := add(value, 32)
    let split_expr_3 := mload(split_expr_2)
}
>

private def copyBlk2 : Stmt := <s
  {
    sstore(split_expr_1, split_expr_3)
    let split_expr_4 := add(slot, 2)
    let split_expr_5 := add(value, 64)
    let split_expr_6 := mload(split_expr_5)
    sstore(split_expr_4, split_expr_6)
}
>

open L2InteropCommitmentTree.Common in
/-- Chunk 1 — field-0 write and field-1 read. -/
private lemma copy_chunk1
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slotArg ptr : Literal}
    (hs : (Ok evm store)["slot"]!! = slotArg)
    (hv : (Ok evm store)["value"]!! = ptr) :
    exec (fuel+1) copyBlk1 (Ok evm store)
      = Ok (evm.sstore slotArg (evm.mload ptr))
          ((((store.insert "split_expr_0" (evm.mload ptr)).insert
              "split_expr_1" (slotArg + 1)).insert
              "split_expr_2" (ptr + 32)).insert
              "split_expr_3" (evm.mload (ptr + 32))) := by
  unfold copyBlk1
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMload', EVMAdd', EVMSstore']
  simp only [multifill_cons, multifill_nil]
  rw [hv]
  simp only [evm_insert, evm_Ok]
  have hok0 : isOk (Ok evm store) := trivial
  have hok1 : isOk ((Ok evm store)⟦"split_expr_0" ↦ evm.mload ptr⟧) := isOk_insert.mpr hok0
  have r1a : ((Ok evm store)⟦"split_expr_0" ↦ evm.mload ptr⟧)["slot"]!! = slotArg := by
    rw [lookup_insert_of_ne (by decide)]; exact hs
  have r1b : ((Ok evm store)⟦"split_expr_0" ↦ evm.mload ptr⟧)["split_expr_0"]!!
      = evm.mload ptr := lookup_insert' hok0
  rw [r1a, r1b]
  set T1 := (Ok evm store)⟦"split_expr_0" ↦ evm.mload ptr⟧ with hT1
  have hok1' : isOk T1 := by rw [hT1]; exact hok1
  set E1 := evm.sstore slotArg (evm.mload ptr) with hE1
  have hokU1 : isOk (T1🇪⟦E1⟧) := by rw [isOk_setEvm]; exact hok1'
  have r2a : (T1🇪⟦E1⟧)["slot"]!! = slotArg := by
    rw [lookup_setEvm_of_isOk hok1']; exact r1a
  rw [r2a]
  have r2b : ((T1🇪⟦E1⟧)⟦"split_expr_1" ↦ slotArg + 1⟧)["value"]!! = ptr := by
    rw [lookup_insert_of_ne (by decide), lookup_setEvm_of_isOk hok1', hT1,
        lookup_insert_of_ne (by decide)]
    exact hv
  rw [r2b]
  have r3 : ((T1🇪⟦E1⟧)⟦"split_expr_1" ↦ slotArg + 1⟧⟦"split_expr_2" ↦ ptr + 32⟧)["split_expr_2"]!!
      = ptr + 32 :=
    lookup_insert' (by rw [isOk_insert, isOk_setEvm]; exact hok1')
  rw [r3]
  try simp only [evm_insert]
  try rw [evm_setEvm_of_isOk hok1']
  try rw [hE1, mload_sstore]
  try rw [hT1]
  try simp only [insert_Ok, setEvm_Ok]

open L2InteropCommitmentTree.Common in
/-- Chunk 2 — field-1 write, field-2 read and write. -/
private lemma copy_chunk2
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slotArg ptr a b : Literal}
    (h1 : (Ok evm store)["split_expr_1"]!! = a)
    (h3 : (Ok evm store)["split_expr_3"]!! = b)
    (hs : (Ok evm store)["slot"]!! = slotArg)
    (hv : (Ok evm store)["value"]!! = ptr) :
    exec (fuel+1) copyBlk2 (Ok evm store)
      = Ok ((evm.sstore a b).sstore (slotArg + 2) (evm.mload (ptr + 64)))
          (((store.insert "split_expr_4" (slotArg + 2)).insert
              "split_expr_5" (ptr + 64)).insert
              "split_expr_6" (evm.mload (ptr + 64))) := by
  unfold copyBlk2
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMload', EVMAdd', EVMSstore']
  simp only [multifill_cons, multifill_nil]
  rw [h1, h3]
  simp only [evm_insert, evm_Ok]
  have hok0 : isOk (Ok evm store) := trivial
  have r1a : ((Ok evm store)🇪⟦evm.sstore a b⟧)["slot"]!! = slotArg := by
    rw [lookup_setEvm_of_isOk hok0]; exact hs
  rw [r1a]
  have r1b : (((Ok evm store)🇪⟦evm.sstore a b⟧)⟦"split_expr_4" ↦ slotArg + 2⟧)["value"]!!
      = ptr := by
    rw [lookup_insert_of_ne (by decide), lookup_setEvm_of_isOk hok0]
    exact hv
  rw [r1b]
  have r2 : (((Ok evm store)🇪⟦evm.sstore a b⟧)⟦"split_expr_4" ↦ slotArg + 2⟧⟦"split_expr_5" ↦ ptr + 64⟧)["split_expr_5"]!!
      = ptr + 64 :=
    lookup_insert' (by rw [isOk_insert, isOk_setEvm]; exact hok0)
  rw [r2]
  try simp only [evm_insert]
  try rw [evm_setEvm_of_isOk hok0]
  try rw [mload_sstore]
  have r3a : ((((Ok evm store)🇪⟦evm.sstore a b⟧)⟦"split_expr_4" ↦ slotArg + 2⟧⟦"split_expr_5" ↦ ptr + 64⟧⟦"split_expr_6" ↦ evm.mload (ptr + 64)⟧))["split_expr_4"]!!
      = slotArg + 2 := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact lookup_insert' (by rw [isOk_setEvm]; exact hok0)
  have r3b : ((((Ok evm store)🇪⟦evm.sstore a b⟧)⟦"split_expr_4" ↦ slotArg + 2⟧⟦"split_expr_5" ↦ ptr + 64⟧⟦"split_expr_6" ↦ evm.mload (ptr + 64)⟧))["split_expr_6"]!!
      = evm.mload (ptr + 64) :=
    lookup_insert' (by rw [isOk_insert, isOk_insert, isOk_setEvm]; exact hok0)
  rw [r3a, r3b]
  try simp only [evm_insert]
  try rw [evm_setEvm_of_isOk hok0]
  try simp only [insert_Ok, setEvm_Ok]

set_option maxHeartbeats 8000000 in
open L2InteropCommitmentTree.Common in
/-- **Closed form of the leaf-struct write** — `copy_struct_to_storage(slot,
ptr)` is exactly three word `sstore`s of the three memory fields
`(value, nextIndex, nextValue)` at `slot`/`slot+1`/`slot+2`. -/
lemma copy_leaf_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slotArg ptr : Literal} :
    execCall (fuel+1) copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf
        [] (Ok evm store, [slotArg, ptr])
      = (Ok evm store).setEvm
          (((evm.sstore slotArg (evm.mload ptr)).sstore
              (slotArg + 1) (evm.mload (ptr + 32))).sstore
              (slotArg + 2) (evm.mload (ptr + 64))) := by
  have hbody : copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf.body
      = [copyBlk1, copyBlk2] := by
    unfold copyBlk1 copyBlk2
    rfl
  have hparams : copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf.params
      = ["slot", "value"] := rfl
  have hrets : copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf.rets = [] := rfl
  unfold execCall call
  simp only [hparams, hrets, hbody]
  simp only [multifill', mkOk_initcall_Ok, List.map_nil, List.map_cons]
  rw [cons, cons, nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["slot", "value"], [slotArg, ptr]⟧) :=
    isOk_initcall_of_isOk trivial
  obtain ⟨e0, σ0, h0⟩ := State_of_isOk hok0
  have hs0 : ((Ok evm store)☎️⟦["slot", "value"], [slotArg, ptr]⟧)["slot"]!!
      = slotArg := lookup_initcall_1
  have hv0 : ((Ok evm store)☎️⟦["slot", "value"], [slotArg, ptr]⟧)["value"]!!
      = ptr := lookup_initcall_2 (by decide)
  have he0 : e0 = evm := by
    have hx := congrArg State.evm h0
    rw [show ((Ok evm store)☎️⟦["slot", "value"], [slotArg, ptr]⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at hx
    exact hx.symm
  rw [h0, he0] at hs0 hv0
  simp only [h0, he0]
  -- chunk 1
  simp only [copy_chunk1 hs0 hv0]
  -- chunk 2 lookups on the post-chunk-1 state
  set σ1 := (((σ0.insert "split_expr_0" (evm.mload ptr)).insert
      "split_expr_1" (slotArg + 1)).insert
      "split_expr_2" (ptr + 32)).insert
      "split_expr_3" (evm.mload (ptr + 32)) with hσ1
  set E1 := evm.sstore slotArg (evm.mload ptr) with hE1
  have h1B : (Ok E1 σ1)["split_expr_1"]!! = slotArg + 1 := by
    rw [hσ1, lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  have h3B : (Ok E1 σ1)["split_expr_3"]!! = evm.mload (ptr + 32) := by
    rw [hσ1]
    exact lookup_insert_self_fin
  have hsB : (Ok E1 σ1)["slot"]!! = slotArg := by
    rw [hσ1, lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_ok_evm E1 evm]
    exact hs0
  have hvB : (Ok E1 σ1)["value"]!! = ptr := by
    rw [hσ1, lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_ok_evm E1 evm]
    exact hv0
  simp only [copy_chunk2 h1B h3B hsB hvB]
  -- normalize the chunk-2 mload through the chunk-1 sstore layer
  rw [hE1, mload_sstore]
  -- rets/state wrappers
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [multifill_nil, setEvm_Ok]


/-! ### The fixed-96 allocation finalizer -/

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

/-- **Closed form of `finalize_allocation_5187(memPtr)`** — the fixed-size-96
allocation finalizer: under the standard pointer bound, exactly
`mstore(64, memPtr + 96)`. -/
lemma finalize_allocation_96_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {p : Literal}
    (hp : p.val + 96 ≤ 18446744073709551615) :
    execCall (fuel+1) finalize_allocation_5187 [] (Ok evm store, [p])
      = (Ok evm store).setEvm (evm.mstore 64 (p + 96)) := by
  unfold execCall call finalize_allocation_5187
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  simp only [cons, nil]
  simp only [If', LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMAdd', EVMGt', EVMLt', EVMOr', EVMMstore']
  simp only [multifill_cons, multifill_nil]
  set B := (Ok evm store)☎️⟦["memPtr"], [p]⟧ with hB
  have hokB : isOk B := isOk_initcall_of_isOk trivial
  have l_mem : B["memPtr"]!! = p := lookup_initcall_1
  rw [l_mem]
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
  have hok0 : isOk (B⟦"newFreePtr" ↦ p + 96⟧) := isOk_insert.mpr hokB
  have l0 : (B⟦"newFreePtr" ↦ p + 96⟧)["newFreePtr"]!! = p + 96 := lookup_insert' hokB
  rw [l0, hgt]
  have hok1 : isOk (B⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_0" ↦ (0 : UInt256)⟧) :=
    isOk_insert.mpr hok0
  have l1a : (B⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_0" ↦ (0 : UInt256)⟧)["newFreePtr"]!!
      = p + 96 := by
    rw [lookup_insert_of_ne (by decide)]; exact l0
  have l1b : (B⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_0" ↦ (0 : UInt256)⟧)["memPtr"]!!
      = p := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]; exact l_mem
  rw [l1a, l1b, hlt]
  have l2a : (B⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_0" ↦ (0 : UInt256)⟧⟦"split_expr_1" ↦ (0 : UInt256)⟧)["split_expr_0"]!!
      = 0 := by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_insert' hok0
  have l2b : (B⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_0" ↦ (0 : UInt256)⟧⟦"split_expr_1" ↦ (0 : UInt256)⟧)["split_expr_1"]!!
      = 0 := lookup_insert' hok1
  rw [l2a, l2b]
  rw [show Fin.lor (0 : UInt256) 0 = (0 : UInt256) from by decide]
  simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  have hok2 : isOk (B⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_0" ↦ (0 : UInt256)⟧⟦"split_expr_1" ↦ (0 : UInt256)⟧) :=
    isOk_insert.mpr hok1
  have l3 : (B⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_0" ↦ (0 : UInt256)⟧⟦"split_expr_1" ↦ (0 : UInt256)⟧)["newFreePtr"]!!
      = p + 96 := by
    rw [lookup_insert_of_ne (by decide)]; exact l1a
  rw [l3]
  have hBevm : B.evm = evm := by
    rw [hB]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  simp only [evm_insert, evm_Ok]
  rw [hBevm]
  have hin_ok : isOk ((B⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_0" ↦ (0 : UInt256)⟧⟦"split_expr_1" ↦ (0 : UInt256)⟧)🇪⟦evm.mstore 64 (p + 96)⟧) := by
    rw [isOk_setEvm]; exact hok2
  rw [reviveJump_of_isOk hin_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = evm.mstore 64 (p + 96) := by
    have h := congrArg State.evm hi
    rw [evm_setEvm_of_isOk hok2] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]
  rfl

/-! ### The leaf-struct read: allocation plus three word `sload`s -/

/-- The evm after `read_from_storage`'s writes: the free-pointer bump and the
three field words copied from storage into the fresh struct at `P`. -/
def leafReadEvm (evm : EVMState) (slot : UInt256) : EVMState :=
  (((evm.mstore 64 (evm.mload 64 + 96)).mstore
      (evm.mload 64) (evm.sload slot)).mstore
      (evm.mload 64 + 32) (evm.sload (slot + 1))).mstore
      (evm.mload 64 + 64) (evm.sload (slot + 2))

private def readBlk1 : Stmt := <s
  {
    let memPtr := mload(64)
    finalize_allocation_5187(memPtr)
    value := memPtr
    let split_expr_0 := sload(slot)
    mstore(memPtr, split_expr_0)
}
>

private def readBlk2 : Stmt := <s
  {
    let split_expr_1 := add(memPtr, 32)
    let split_expr_2 := add(slot, 1)
    let split_expr_3 := sload(split_expr_2)
    mstore(split_expr_1, split_expr_3)
    let split_expr_4 := add(memPtr, 64)
}
>

private def readBlk3 : Stmt := <s
  {
    let split_expr_5 := add(slot, 2)
    let split_expr_6 := sload(split_expr_5)
    mstore(split_expr_4, split_expr_6)
}
>

open L2InteropCommitmentTree.Common in
/-- Chunk 1 — allocate, record the pointer, copy field 0. -/
private lemma read_chunk1
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slotArg : Literal}
    (hs : (Ok evm store)["slot"]!! = slotArg)
    (hp : (evm.mload 64).val + 96 ≤ 18446744073709551615) :
    exec (fuel+1) readBlk1 (Ok evm store)
      = Ok ((evm.mstore 64 (evm.mload 64 + 96)).mstore (evm.mload 64) (evm.sload slotArg))
          (((store.insert "memPtr" (evm.mload 64)).insert
              "value" (evm.mload 64)).insert
              "split_expr_0" (evm.sload slotArg)) := by
  unfold readBlk1
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', Assign', ExprStmtPrimCall', ExprStmtCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMload', EVMSload', EVMMstore']
  simp only [multifill_cons, multifill_nil]
  simp only [evm_insert, evm_Ok]
  have hok0 : isOk (Ok evm store) := trivial
  have hok1 : isOk ((Ok evm store)⟦"memPtr" ↦ evm.mload 64⟧) := isOk_insert.mpr hok0
  have r1 : ((Ok evm store)⟦"memPtr" ↦ evm.mload 64⟧)["memPtr"]!! = evm.mload 64 :=
    lookup_insert' hok0
  rw [r1]
  simp only [insert_Ok]
  rw [finalize_allocation_96_call hp]
  set B := Ok evm (Finmap.insert "memPtr" (evm.mload 64) store) with hB
  have hokB : isOk B := by rw [hB]; trivial
  set E0 := evm.mstore 64 (evm.mload 64 + 96) with hE0
  have r2 : (B🇪⟦E0⟧)["memPtr"]!! = evm.mload 64 := by
    rw [lookup_setEvm_of_isOk hokB, hB]
    exact lookup_insert_self_fin
  rw [r2]
  have r3 : ((B🇪⟦E0⟧)⟦"value" ↦ evm.mload 64⟧)["slot"]!! = slotArg := by
    rw [lookup_insert_of_ne (by decide), lookup_setEvm_of_isOk hokB, hB,
        lookup_insert_ne_fin (by decide)]
    exact hs
  rw [r3]
  try simp only [evm_insert]
  try rw [evm_setEvm_of_isOk hokB]
  try rw [hE0]
  rw [sload_mstore]
  have r4a : ((B🇪⟦E0⟧)⟦"value" ↦ evm.mload 64⟧⟦"split_expr_0" ↦ evm.sload slotArg⟧)["memPtr"]!!
      = evm.mload 64 := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
        lookup_setEvm_of_isOk hokB, hB]
    exact lookup_insert_self_fin
  have r4b : ((B🇪⟦E0⟧)⟦"value" ↦ evm.mload 64⟧⟦"split_expr_0" ↦ evm.sload slotArg⟧)["split_expr_0"]!!
      = evm.sload slotArg :=
    lookup_insert' (by rw [isOk_insert, isOk_setEvm]; exact hokB)
  rw [r4a, r4b]
  try simp only [evm_insert]
  try rw [evm_setEvm_of_isOk hokB]
  try rw [hE0]
  rw [hB]
  try simp only [insert_Ok, setEvm_Ok]

open L2InteropCommitmentTree.Common in
/-- Chunk 2 — copy field 1, stage the field-2 pointer. -/
private lemma read_chunk2
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {P slotArg : Literal}
    (hm : (Ok evm store)["memPtr"]!! = P)
    (hs : (Ok evm store)["slot"]!! = slotArg) :
    exec (fuel+1) readBlk2 (Ok evm store)
      = Ok (evm.mstore (P + 32) (evm.sload (slotArg + 1)))
          ((((store.insert "split_expr_1" (P + 32)).insert
              "split_expr_2" (slotArg + 1)).insert
              "split_expr_3" (evm.sload (slotArg + 1))).insert
              "split_expr_4" (P + 64)) := by
  unfold readBlk2
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMAdd', EVMSload', EVMMstore']
  simp only [multifill_cons, multifill_nil]
  rw [hm]
  simp only [evm_insert, evm_Ok]
  have hok0 : isOk (Ok evm store) := trivial
  have hok1 : isOk ((Ok evm store)⟦"split_expr_1" ↦ P + 32⟧) := isOk_insert.mpr hok0
  have r1 : ((Ok evm store)⟦"split_expr_1" ↦ P + 32⟧)["slot"]!! = slotArg := by
    rw [lookup_insert_of_ne (by decide)]; exact hs
  rw [r1]
  have r1c : ((Ok evm store)⟦"split_expr_1" ↦ P + 32⟧⟦"split_expr_2" ↦ slotArg + 1⟧)["split_expr_2"]!!
      = slotArg + 1 := lookup_insert' hok1
  rw [r1c]
  have r2a : ((Ok evm store)⟦"split_expr_1" ↦ P + 32⟧⟦"split_expr_2" ↦ slotArg + 1⟧⟦"split_expr_3" ↦ evm.sload (slotArg + 1)⟧)["split_expr_1"]!!
      = P + 32 := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact lookup_insert' hok0
  have r2b : ((Ok evm store)⟦"split_expr_1" ↦ P + 32⟧⟦"split_expr_2" ↦ slotArg + 1⟧⟦"split_expr_3" ↦ evm.sload (slotArg + 1)⟧)["split_expr_3"]!!
      = evm.sload (slotArg + 1) :=
    lookup_insert' (by rw [isOk_insert, isOk_insert]; exact hok0)
  rw [r2a, r2b]
  have r3 : (((Ok evm store)⟦"split_expr_1" ↦ P + 32⟧⟦"split_expr_2" ↦ slotArg + 1⟧⟦"split_expr_3" ↦ evm.sload (slotArg + 1)⟧)🇪⟦evm.mstore (P + 32) (evm.sload (slotArg + 1))⟧)["memPtr"]!!
      = P := by
    rw [lookup_setEvm_of_isOk (by rw [isOk_insert, isOk_insert, isOk_insert]; exact hok0),
        lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
        lookup_insert_of_ne (by decide)]
    exact hm
  rw [r3]
  try simp only [evm_insert]
  try rw [evm_setEvm_of_isOk (by rw [isOk_insert, isOk_insert, isOk_insert]; exact hok0)]
  try simp only [insert_Ok, setEvm_Ok]

open L2InteropCommitmentTree.Common in
/-- Chunk 3 — copy field 2. -/
private lemma read_chunk3
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {q slotArg : Literal}
    (hs : (Ok evm store)["slot"]!! = slotArg)
    (h4 : (Ok evm store)["split_expr_4"]!! = q) :
    exec (fuel+1) readBlk3 (Ok evm store)
      = Ok (evm.mstore q (evm.sload (slotArg + 2)))
          ((store.insert "split_expr_5" (slotArg + 2)).insert
              "split_expr_6" (evm.sload (slotArg + 2))) := by
  unfold readBlk3
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMAdd', EVMSload', EVMMstore']
  simp only [multifill_cons, multifill_nil]
  rw [hs]
  simp only [evm_insert, evm_Ok]
  have hok0 : isOk (Ok evm store) := trivial
  have r1a : ((Ok evm store)⟦"split_expr_5" ↦ slotArg + 2⟧)["split_expr_5"]!!
      = slotArg + 2 := lookup_insert' hok0
  rw [r1a]
  have r2a : ((Ok evm store)⟦"split_expr_5" ↦ slotArg + 2⟧⟦"split_expr_6" ↦ evm.sload (slotArg + 2)⟧)["split_expr_4"]!!
      = q := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact h4
  have r2b : ((Ok evm store)⟦"split_expr_5" ↦ slotArg + 2⟧⟦"split_expr_6" ↦ evm.sload (slotArg + 2)⟧)["split_expr_6"]!!
      = evm.sload (slotArg + 2) :=
    lookup_insert' (by rw [isOk_insert]; exact hok0)
  rw [r2a, r2b]
  try simp only [evm_insert]
  try simp only [insert_Ok, setEvm_Ok]

set_option maxHeartbeats 8000000 in
open L2InteropCommitmentTree.Common in
/-- **Closed form of the leaf-struct read** — `read_from_storage(slot)`
allocates a fresh 96-byte struct at the free pointer and copies the three
storage words `(value, nextIndex, nextValue)` from `slot`/`slot+1`/`slot+2`
into it, returning the pointer. -/
lemma read_leaf_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {slotArg : Literal} {v : Identifier}
    (hp : (evm.mload 64).val + 96 ≤ 18446744073709551615) :
    execCall (fuel+1) read_from_storage_reference_type_struct_IMTLeaf
        [v] (Ok evm store, [slotArg])
      = Ok (leafReadEvm evm slotArg) (store.insert v (evm.mload 64)) := by
  have hbody : read_from_storage_reference_type_struct_IMTLeaf.body
      = [readBlk1, readBlk2, readBlk3] := by
    unfold readBlk1 readBlk2 readBlk3
    rfl
  have hparams : read_from_storage_reference_type_struct_IMTLeaf.params = ["slot"] := rfl
  have hrets : read_from_storage_reference_type_struct_IMTLeaf.rets = ["value"] := rfl
  unfold execCall call
  simp only [hparams, hrets, hbody]
  simp only [multifill', mkOk_initcall_Ok, List.map_nil, List.map_cons]
  rw [cons, cons, cons, nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["slot"], [slotArg]⟧) := isOk_initcall_of_isOk trivial
  obtain ⟨e0, σ0, h0⟩ := State_of_isOk hok0
  have hs0 : ((Ok evm store)☎️⟦["slot"], [slotArg]⟧)["slot"]!! = slotArg := lookup_initcall_1
  have he0 : e0 = evm := by
    have hx := congrArg State.evm h0
    rw [show ((Ok evm store)☎️⟦["slot"], [slotArg]⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at hx
    exact hx.symm
  rw [h0, he0] at hs0
  simp only [h0, he0]
  -- chunk 1
  simp only [read_chunk1 hs0 hp]
  -- chunk 2 lookups
  set σ1 := ((σ0.insert "memPtr" (evm.mload 64)).insert
      "value" (evm.mload 64)).insert "split_expr_0" (evm.sload slotArg) with hσ1
  set E1 := (evm.mstore 64 (evm.mload 64 + 96)).mstore (evm.mload 64) (evm.sload slotArg) with hE1
  have hmB : (Ok E1 σ1)["memPtr"]!! = evm.mload 64 := by
    rw [hσ1, lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  have hsB : (Ok E1 σ1)["slot"]!! = slotArg := by
    rw [hσ1, lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_ok_evm E1 evm]
    exact hs0
  simp only [read_chunk2 hmB hsB]
  -- normalize the chunk-2 sload through the chunk-1 mstores
  rw [hE1, sload_mstore, sload_mstore]
  -- chunk 3 lookups
  set σ2 := (((σ1.insert "split_expr_1" (evm.mload 64 + 32)).insert
      "split_expr_2" (slotArg + 1)).insert
      "split_expr_3" (evm.sload (slotArg + 1))).insert
      "split_expr_4" (evm.mload 64 + 64) with hσ2
  set E2 := ((evm.mstore 64 (evm.mload 64 + 96)).mstore (evm.mload 64) (evm.sload slotArg)).mstore
      (evm.mload 64 + 32) (evm.sload (slotArg + 1)) with hE2
  have hsC : (Ok E2 σ2)["slot"]!! = slotArg := by
    rw [hσ2, lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_ok_evm E2 E1]
    exact hsB
  have h4C : (Ok E2 σ2)["split_expr_4"]!! = evm.mload 64 + 64 := by
    rw [hσ2]
    exact lookup_insert_self_fin
  simp only [read_chunk3 hsC h4C]
  -- normalize the chunk-3 sload through the three mstores
  rw [hE2, sload_mstore, sload_mstore, sload_mstore]
  -- rets lookup + call wrappers
  have hvar : (Ok ((((evm.mstore 64 (evm.mload 64 + 96)).mstore (evm.mload 64) (evm.sload slotArg)).mstore
      (evm.mload 64 + 32) (evm.sload (slotArg + 1))).mstore
      (evm.mload 64 + 64) (evm.sload (slotArg + 2)))
      ((σ2.insert "split_expr_5" (slotArg + 2)).insert
        "split_expr_6" (evm.sload (slotArg + 2))))["value"]!! = evm.mload 64 := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hσ2,
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hσ1,
        lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  simp only [hvar]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [multifill_cons, multifill_nil, insert_Ok]
  rfl


/-! ### `sload` after `sstore` — the pointwise frame algebra

The general storage round-trip laws of the model.  `sload_sstore_ne` is
unconditional; the self law needs only the standard deployed-contract fact
(the executing account exists) — it holds even for zero values, because the
model's `updateStorage 0` erases the key and a missing key reads as 0. -/

/-- `sstore` does not change the execution environment. -/
private lemma execution_env_sstore (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).execution_env = σ.execution_env := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-- The executing account survives an `sstore` (it is re-inserted updated). -/
lemma acct_sstore {σ : EVMState} {a v : UInt256}
    (hacc : (σ.lookupAccount σ.execution_env.code_owner).isSome) :
    ((σ.sstore a v).lookupAccount
        ((σ.sstore a v).execution_env.code_owner)).isSome := by
  rw [execution_env_sstore]
  unfold EVMState.sstore
  cases h : σ.lookupAccount σ.execution_env.code_owner with
  | none => exact hacc
  | some act =>
    show ((σ.updateAccount σ.execution_env.code_owner
        (act.updateStorage a v)).lookupAccount σ.execution_env.code_owner).isSome
    unfold EVMState.lookupAccount EVMState.updateAccount
    simp only [Finmap.lookup_insert]
    rfl

/-- **Self round-trip**: re-reading the slot just written returns the stored
value (any value — the zero case erases and reads back 0). -/
lemma sload_sstore_self {σ : EVMState} {a v : UInt256}
    (hacc : (σ.lookupAccount σ.execution_env.code_owner).isSome) :
    (σ.sstore a v).sload a = v := by
  unfold EVMState.sstore EVMState.sload
  cases h : σ.lookupAccount σ.execution_env.code_owner with
  | none => rw [h] at hacc; simp at hacc
  | some act =>
    simp only [h]
    show (match ((σ.updateAccount σ.execution_env.code_owner
        (act.updateStorage a v)).lookupAccount σ.execution_env.code_owner) with
      | .some act => act.lookupStorage a
      | .none => 0) = v
    unfold EVMState.lookupAccount EVMState.updateAccount
    simp only [Finmap.lookup_insert]
    unfold Account.updateStorage Account.lookupStorage
    by_cases hv : v = 0
    · rw [if_pos (by simpa using hv)]
      simp only [Finmap.lookup_erase]
      exact hv.symm
    · rw [if_neg (by simpa using hv), Finmap.lookup_insert]

/-- **Distinct-slot frame**: writing one slot leaves every other slot's read
unchanged (unconditional — a missing account makes `sstore` a no-op). -/
lemma sload_sstore_ne {σ : EVMState} {a v r : UInt256}
    (hne : a ≠ r) :
    (σ.sstore a v).sload r = σ.sload r := by
  unfold EVMState.sstore EVMState.sload
  cases h : σ.lookupAccount σ.execution_env.code_owner with
  | none => simp only [h]
  | some act =>
    simp only [h]
    show (match ((σ.updateAccount σ.execution_env.code_owner
        (act.updateStorage a v)).lookupAccount σ.execution_env.code_owner) with
      | .some act => act.lookupStorage r
      | .none => 0) = act.lookupStorage r
    unfold EVMState.lookupAccount EVMState.updateAccount
    simp only [Finmap.lookup_insert]
    unfold Account.updateStorage Account.lookupStorage
    by_cases hv : v = 0
    · rw [if_pos (by simpa using hv)]
      rw [Finmap.lookup_erase_ne (Ne.symm hne)]
    · rw [if_neg (by simpa using hv), Finmap.lookup_insert_of_ne _ (Ne.symm hne)]

/-! ### The leaf abstraction and the insert writes' pointwise effect -/

/-- The abstract leaf represented at base slot `b`: field 0 is the key
(`value`), field 2 the gap witness (`nextValue`). -/
def leafAt (σ : EVMState) (b : UInt256) : IMTAbstract.AbsLeaf :=
  ⟨σ.sload b, σ.sload (b + 2)⟩

/-- The three-word leaf-struct write (the evm `copy_leaf_call` produces, with
the memory fields instantiated). -/
def writeLeafEvm (σ : EVMState) (b m0 m1 m2 : UInt256) : EVMState :=
  ((σ.sstore b m0).sstore (b + 1) m1).sstore (b + 2) m2

/-- **Self readback**: after writing a leaf struct at `b`, the represented
leaf at `b` is exactly `⟨m0, m2⟩`. -/
theorem leafAt_write_self
    {σ : EVMState} {b m0 m1 m2 : UInt256}
    (hacc : (σ.lookupAccount σ.execution_env.code_owner).isSome)
    (h01 : b ≠ b + 1) (h02 : b ≠ b + 2) (h12 : b + 1 ≠ b + 2) :
    leafAt (writeLeafEvm σ b m0 m1 m2) b = ⟨m0, m2⟩ := by
  unfold leafAt writeLeafEvm
  have f0 : (((σ.sstore b m0).sstore (b + 1) m1).sstore (b + 2) m2).sload b = m0 := by
    rw [sload_sstore_ne (Ne.symm h02), sload_sstore_ne (Ne.symm h01)]
    exact sload_sstore_self hacc
  have f2 : (((σ.sstore b m0).sstore (b + 1) m1).sstore (b + 2) m2).sload (b + 2) = m2 :=
    sload_sstore_self (acct_sstore (acct_sstore hacc))
  rw [f0, f2]

/-- **Frame**: a leaf-struct write at `b` leaves the represented leaf at any
slot-disjoint base `c` unchanged. -/
theorem leafAt_write_frame
    {σ : EVMState} {b m0 m1 m2 c : UInt256}
    (hb0 : b ≠ c) (hb1 : b + 1 ≠ c) (hb2 : b + 2 ≠ c)
    (hb0' : b ≠ c + 2) (hb1' : b + 1 ≠ c + 2) (hb2' : b + 2 ≠ c + 2) :
    leafAt (writeLeafEvm σ b m0 m1 m2) c = leafAt σ c := by
  unfold leafAt writeLeafEvm
  rw [sload_sstore_ne hb2, sload_sstore_ne hb1, sload_sstore_ne hb0,
      sload_sstore_ne hb2', sload_sstore_ne hb1', sload_sstore_ne hb0']

/-- **THE INSERT WRITES, pointwise.**  After the glue's two struct writes —
the retargeted low leaf `(lv, ni, v)` at `lowB`, then the new leaf
`(v, oi, ov)` at `newB` — the represented leaves are exactly the retarget
`⟨lv, v⟩` at `lowB`, the new leaf `⟨v, ov⟩` at `newB`, and unchanged
everywhere slot-disjoint: precisely hypotheses (i)–(iii) of the abstract
insert-effect bridge (`IMTAbstract.image_insert_effect`, #40). -/
theorem insert_writes_readback
    {σ : EVMState} {lowB newB lv ni v oi ov : UInt256}
    (hacc : (σ.lookupAccount σ.execution_env.code_owner).isSome)
    -- in-triple distinctness (no wraparound of the two bases)
    (hl01 : lowB ≠ lowB + 1) (hl02 : lowB ≠ lowB + 2) (hl12 : lowB + 1 ≠ lowB + 2)
    (hn01 : newB ≠ newB + 1) (hn02 : newB ≠ newB + 2) (hn12 : newB + 1 ≠ newB + 2)
    -- cross-triple disjointness (distinct keccak-separated bases)
    (hx0 : newB ≠ lowB) (hx1 : newB + 1 ≠ lowB) (hx2 : newB + 2 ≠ lowB)
    (hx0' : newB ≠ lowB + 2) (hx1' : newB + 1 ≠ lowB + 2) (hx2' : newB + 2 ≠ lowB + 2) :
    leafAt (writeLeafEvm (writeLeafEvm σ lowB lv ni v) newB v oi ov) lowB
        = ⟨lv, v⟩
      ∧ leafAt (writeLeafEvm (writeLeafEvm σ lowB lv ni v) newB v oi ov) newB
        = ⟨v, ov⟩
      ∧ ∀ c : UInt256,
          lowB ≠ c → lowB + 1 ≠ c → lowB + 2 ≠ c →
          lowB ≠ c + 2 → lowB + 1 ≠ c + 2 → lowB + 2 ≠ c + 2 →
          newB ≠ c → newB + 1 ≠ c → newB + 2 ≠ c →
          newB ≠ c + 2 → newB + 1 ≠ c + 2 → newB + 2 ≠ c + 2 →
          leafAt (writeLeafEvm (writeLeafEvm σ lowB lv ni v) newB v oi ov) c
            = leafAt σ c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [leafAt_write_frame hx0 hx1 hx2 hx0' hx1' hx2']
    exact leafAt_write_self hacc hl01 hl02 hl12
  · exact leafAt_write_self (acct_sstore (acct_sstore (acct_sstore hacc)))
      hn01 hn02 hn12
  · intro c hc0 hc1 hc2 hc0' hc1' hc2' hd0 hd1 hd2 hd0' hd1' hd2'
    rw [leafAt_write_frame hd0 hd1 hd2 hd0' hd1' hd2',
        leafAt_write_frame hc0 hc1 hc2 hc0' hc1' hc2']


/-! ### Keccak base separation — distinct keys give disjoint slot triples

The two remaining arithmetic inputs to the insert chain: the leaf bases of
DISTINCT indices are separated beyond any small offset (A6″ `slot_sep`), and
a base's own triple is internally distinct.  Together with #41's pointwise
readback these discharge every slot-side hypothesis of the insert-effect
bridge (#40). -/

/-- Element 0 of a `[0,64)` interval is the word at address 0 — two intervals
differ if their key words differ. -/
private lemma mkInterval_0_64_ne_of_word0_ne
    {ms_v ms_i : MachineState}
    (h0 : ms_v.lookupMemory (0 : UInt256) ≠ ms_i.lookupMemory (0 : UInt256)) :
    EVMState.mkInterval ms_v 0 64 ≠ EVMState.mkInterval ms_i 0 64 := by
  intro heq
  apply h0
  have ev : ∀ ms : MachineState,
      (EVMState.mkInterval ms 0 64).get? 0 = some (ms.lookupMemory (0 : UInt256)) := by
    intro ms
    unfold EVMState.mkInterval
    simp only [List.get?_map]
    have hidx : (List.range' (↑(0 : UInt256)) (↑(64 : UInt256))).get? 0 = some 0 := by
      decide
    rw [hidx]
    rfl
  have h := ev ms_v
  rw [heq, ev ms_i] at h
  exact (Option.some.inj h).symm

/-- The mapping accessor's scratch reads the key back at address 0 (the base
word at 32 does not touch `[0, 32)`). -/
private lemma accessor_key_readback (σ : EVMState) (k b : UInt256) :
    ((σ.mstore 0 k).mstore 32 b).machine_state.lookupMemory (0 : UInt256) = k := by
  show ((σ.machine_state.updateMemory 0 k).updateMemory 32 b).lookupMemory (0 : UInt256) = k
  have h32v : ((32 : UInt256)).val = 32 := by decide
  have h0v : ((0 : UInt256)).val = 0 := by decide
  rw [lookupMemory_updateMemory_outside _ 32 b 0
      (by rw [h32v]; norm_num) (by rw [h0v]; norm_num)
      (by left; rw [h0v, h32v])]
  exact lookupMemory_updateMemory_self' _ 0 k (by rw [h0v]; norm_num)

/-- An offset never aliases a different offset over the same base. -/
lemma base_offset_ne {b i j : UInt256} (hij : i ≠ j) : b + i ≠ b + j :=
  fun h => hij (add_left_cancel h)

/-- **KECCAK BASE SEPARATION (A6″).**  The leaf-slot bases of two DISTINCT
keys — both computed by the mapping accessor `keccak256(key ‖ base)` over
the same mapping base word — never collide at any pair of small offsets:
`b₁ + i ≠ b₂ + j` for `i, j < 2³²`.  This is the slot-disjointness the
insert writes (#41) and the walk stores rely on. -/
theorem leafBase_sep
    {σ₁ σ₂ σ₁' σ₂' : EVMState} {k₁ k₂ bs b₁ b₂ : UInt256} (i j : UInt256)
    (h₁ : ((σ₁.mstore 0 k₁).mstore 32 bs).keccak256 0 64 = some (b₁, σ₁'))
    (h₂ : ((σ₂.mstore 0 k₂).mstore 32 bs).keccak256 0 64 = some (b₂, σ₂'))
    (hk : k₁ ≠ k₂)
    (hi : i.val < Clear.KeccakInjective.lowSlotBound)
    (hj : j.val < Clear.KeccakInjective.lowSlotBound) :
    b₁ + i ≠ b₂ + j := by
  have hint : EVMState.mkInterval ((σ₁.mstore 0 k₁).mstore 32 bs).machine_state 0 64
      ≠ EVMState.mkInterval ((σ₂.mstore 0 k₂).mstore 32 bs).machine_state 0 64 := by
    apply mkInterval_0_64_ne_of_word0_ne
    rw [accessor_key_readback, accessor_key_readback]
    exact hk
  have hbound : Clear.KeccakInjective.lowSlotBound = 2 ^ 32 := rfl
  have hsz : UInt256.size = 2 ^ 256 := by norm_num
  intro heq
  rcases le_or_lt j.val i.val with hle | hlt
  · -- shift the difference onto b₁'s side
    set d := i - j with hd
    have hjd : j + d = i := by
      rw [hd, add_comm]
      exact sub_add_cancel i j
    have hdval : d.val = i.val - j.val := by
      have h : d.val = (i.val + (UInt256.size - j.val)) % UInt256.size := rfl
      have hjs : j.val ≤ UInt256.size := le_of_lt j.isLt
      have his := i.isLt
      have hrw : i.val + (UInt256.size - j.val) = UInt256.size + (i.val - j.val) := by
        omega
      rw [h, hrw, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)

    have hstep : b₁ + d = b₂ := by
      have h' : (b₁ + d) + j = b₂ + j := by
        rw [add_assoc, add_comm d j, hjd]
        exact heq
      exact add_right_cancel h'
    exact Clear.KeccakInjective.keccak256_slot_sep h₁ h₂ hint
      (by rw [hbound, hdval]; omega) hstep
  · -- symmetric: shift onto b₂'s side
    set e := j - i with he
    have hie : i + e = j := by
      rw [he, add_comm]
      exact sub_add_cancel j i
    have heval : e.val = j.val - i.val := by
      have h : e.val = (j.val + (UInt256.size - i.val)) % UInt256.size := rfl
      have his : i.val ≤ UInt256.size := le_of_lt i.isLt
      have hjs := j.isLt
      have hrw : j.val + (UInt256.size - i.val) = UInt256.size + (j.val - i.val) := by
        omega
      rw [h, hrw, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    have hstep : b₂ + e = b₁ := by
      have h' : (b₂ + e) + i = b₁ + i := by
        rw [add_assoc, add_comm e i, hie]
        exact heq.symm
      exact add_right_cancel h'
    exact Clear.KeccakInjective.keccak256_slot_sep h₂ h₁ hint.symm
      (by rw [hbound, heval]; omega) hstep


/-! ### THE CONCRETE INSERT STEP — writes to `imtInsert`, end to end

Composing the pointwise readback (#41), the base separation (above), and the
abstract insert-effect bridge (#40): the glue's two struct writes transform
the REPRESENTED LEAF SET into exactly `imtInsert`, preserving the sortedness
invariants — one `Evolution` step (#34/#35), stated directly over the
storage model. -/

private lemma tri01 (b : UInt256) : b ≠ b + 1 := by
  intro h
  have h' : b + 0 = b + 1 := by rw [add_zero]; exact h
  exact (by decide : (0 : UInt256) ≠ 1) (add_left_cancel h')

private lemma tri02 (b : UInt256) : b ≠ b + 2 := by
  intro h
  have h' : b + 0 = b + 2 := by rw [add_zero]; exact h
  exact (by decide : (0 : UInt256) ≠ 2) (add_left_cancel h')

private lemma tri12 (b : UInt256) : b + 1 ≠ b + 2 :=
  fun h => (by decide : (1 : UInt256) ≠ 2) (add_left_cancel h)

/-- Unpack a pairwise triple-separation fact into the six `≠`s the frame
lemma consumes. -/
private lemma sepN {b c : UInt256}
    (h : ∀ i j : UInt256, i.val < 3 → j.val < 3 → b + i ≠ c + j) :
    (b ≠ c) ∧ (b + 1 ≠ c) ∧ (b + 2 ≠ c)
      ∧ (b ≠ c + 2) ∧ (b + 1 ≠ c + 2) ∧ (b + 2 ≠ c + 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := h 0 0 (by decide) (by decide); rwa [add_zero, add_zero] at this
  · have := h 1 0 (by decide) (by decide); rwa [add_zero] at this
  · have := h 2 0 (by decide) (by decide); rwa [add_zero] at this
  · have := h 0 2 (by decide) (by decide); rwa [add_zero] at this
  · exact h 1 2 (by decide) (by decide)
  · exact h 2 2 (by decide) (by decide)

/-- **THE INSERT STEP, concretely.**  Under the deployed-contract fact,
pairwise triple separation of the (grown) base set, and uniqueness of the
low leaf's representation: after the glue's two struct writes — the
retargeted low leaf `(sload lowB, ni, v)` at `lowB` and the new leaf
`(v, oi, sload (lowB+2))` at `newB` — the represented leaf set over the
grown base set IS `imtInsert`, and it remains `GapSound` and `KeyInj`. -/
theorem leaves_insert_step
    {σ : EVMState} {bases : Finset UInt256} {lowB newB ni oi v : UInt256}
    (hacc : (σ.lookupAccount σ.execution_env.code_owner).isSome)
    (hnew : newB ∉ bases) (hlow : lowB ∈ bases)
    (hsep : ∀ b ∈ insert newB bases, ∀ c ∈ insert newB bases, b ≠ c →
        ∀ i j : UInt256, i.val < 3 → j.val < 3 → b + i ≠ c + j)
    (huniq : ∀ b ∈ bases, b ≠ lowB → leafAt σ b ≠ leafAt σ lowB)
    (hgs : IMTAbstract.GapSound (bases.image (leafAt σ)))
    (hinj : IMTAbstract.KeyInj (bases.image (leafAt σ)))
    (hwlow : (leafAt σ lowB).key < v)
    (hwin : (leafAt σ lowB).nextKey = 0 ∨ v < (leafAt σ lowB).nextKey) :
    (insert newB bases).image
        (leafAt (writeLeafEvm (writeLeafEvm σ lowB (σ.sload lowB) ni v)
          newB v oi (σ.sload (lowB + 2))))
        = IMTAbstract.imtInsert (bases.image (leafAt σ)) (leafAt σ lowB) v
      ∧ IMTAbstract.GapSound ((insert newB bases).image
          (leafAt (writeLeafEvm (writeLeafEvm σ lowB (σ.sload lowB) ni v)
            newB v oi (σ.sload (lowB + 2)))))
      ∧ IMTAbstract.KeyInj ((insert newB bases).image
          (leafAt (writeLeafEvm (writeLeafEvm σ lowB (σ.sload lowB) ni v)
            newB v oi (σ.sload (lowB + 2))))) := by
  have hne_nl : newB ≠ lowB := fun h => hnew (h ▸ hlow)
  have hcross := sepN (hsep newB (Finset.mem_insert_self _ _)
    lowB (Finset.mem_insert.mpr (Or.inr hlow)) hne_nl)
  have hrb := insert_writes_readback
    (σ := σ) (lowB := lowB) (newB := newB)
    (lv := σ.sload lowB) (ni := ni) (v := v) (oi := oi) (ov := σ.sload (lowB + 2))
    hacc
    (tri01 lowB) (tri02 lowB) (tri12 lowB)
    (tri01 newB) (tri02 newB) (tri12 newB)
    hcross.1 hcross.2.1 hcross.2.2.1
    hcross.2.2.2.1 hcross.2.2.2.2.1 hcross.2.2.2.2.2
  exact IMTAbstract.image_insert_step hnew hlow
    (by
      show leafAt _ lowB = ⟨(leafAt σ lowB).key, v⟩
      exact hrb.1)
    (by
      show leafAt _ newB = ⟨v, (leafAt σ lowB).nextKey⟩
      exact hrb.2.1)
    (by
      intro b hb hbl
      have hbmem : b ∈ insert newB bases := Finset.mem_insert.mpr (Or.inr hb)
      have hlmem : lowB ∈ insert newB bases := Finset.mem_insert.mpr (Or.inr hlow)
      have hnmem : newB ∈ insert newB bases := Finset.mem_insert_self _ _
      have hne_nb : newB ≠ b := fun h => hnew (h ▸ hb)
      have hL := sepN (hsep lowB hlmem b hbmem (Ne.symm hbl))
      have hN := sepN (hsep newB hnmem b hbmem hne_nb)
      exact hrb.2.2 b
        hL.1 hL.2.1 hL.2.2.1 hL.2.2.2.1 hL.2.2.2.2.1 hL.2.2.2.2.2
        hN.1 hN.2.1 hN.2.2.1 hN.2.2.2.1 hN.2.2.2.2.1 hN.2.2.2.2.2)
    huniq hgs hinj hwlow hwin


/-! ### The fully-inductive concrete step, and concrete histories

`leaves_insert_step'` re-states #42 with the uniqueness hypothesis replaced
by the inductive `RepKeyInj` (which it also carries forward).  On top of it,
`ConcreteStep`/`concrete_history`: ANY sequence of such storage transitions
from a sound base is an `Evolution` with all four invariants at every
snapshot — the abstract temporal theorems (#34 never-both, #35
never-neither) apply to the concrete tree with no further hypotheses. -/

/-- **The fully-inductive insert step** — #42 with `RepKeyInj` in place of
the uniqueness hypothesis, and carried to the new state. -/
theorem leaves_insert_step'
    {σ : EVMState} {bases : Finset UInt256} {lowB newB ni oi v : UInt256}
    (hacc : (σ.lookupAccount σ.execution_env.code_owner).isSome)
    (hnew : newB ∉ bases) (hlow : lowB ∈ bases)
    (hsep : ∀ b ∈ insert newB bases, ∀ c ∈ insert newB bases, b ≠ c →
        ∀ i j : UInt256, i.val < 3 → j.val < 3 → b + i ≠ c + j)
    (hrki : IMTAbstract.RepKeyInj (leafAt σ) bases)
    (hgs : IMTAbstract.GapSound (bases.image (leafAt σ)))
    (hinj : IMTAbstract.KeyInj (bases.image (leafAt σ)))
    (hwlow : (leafAt σ lowB).key < v)
    (hwin : (leafAt σ lowB).nextKey = 0 ∨ v < (leafAt σ lowB).nextKey) :
    (insert newB bases).image
        (leafAt (writeLeafEvm (writeLeafEvm σ lowB (σ.sload lowB) ni v)
          newB v oi (σ.sload (lowB + 2))))
        = IMTAbstract.imtInsert (bases.image (leafAt σ)) (leafAt σ lowB) v
      ∧ IMTAbstract.GapSound ((insert newB bases).image
          (leafAt (writeLeafEvm (writeLeafEvm σ lowB (σ.sload lowB) ni v)
            newB v oi (σ.sload (lowB + 2)))))
      ∧ IMTAbstract.KeyInj ((insert newB bases).image
          (leafAt (writeLeafEvm (writeLeafEvm σ lowB (σ.sload lowB) ni v)
            newB v oi (σ.sload (lowB + 2)))))
      ∧ IMTAbstract.RepKeyInj
          (leafAt (writeLeafEvm (writeLeafEvm σ lowB (σ.sload lowB) ni v)
            newB v oi (σ.sload (lowB + 2)))) (insert newB bases) := by
  have hne_nl : newB ≠ lowB := fun h => hnew (h ▸ hlow)
  have hcross := sepN (hsep newB (Finset.mem_insert_self _ _)
    lowB (Finset.mem_insert.mpr (Or.inr hlow)) hne_nl)
  have hrb := insert_writes_readback
    (σ := σ) (lowB := lowB) (newB := newB)
    (lv := σ.sload lowB) (ni := ni) (v := v) (oi := oi) (ov := σ.sload (lowB + 2))
    hacc
    (tri01 lowB) (tri02 lowB) (tri12 lowB)
    (tri01 newB) (tri02 newB) (tri12 newB)
    hcross.1 hcross.2.1 hcross.2.2.1
    hcross.2.2.2.1 hcross.2.2.2.2.1 hcross.2.2.2.2.2
  exact IMTAbstract.image_insert_step' hnew hlow
    (by
      show leafAt _ lowB = ⟨(leafAt σ lowB).key, v⟩
      exact hrb.1)
    (by
      show leafAt _ newB = ⟨v, (leafAt σ lowB).nextKey⟩
      exact hrb.2.1)
    (by
      intro b hb hbl
      have hbmem : b ∈ insert newB bases := Finset.mem_insert.mpr (Or.inr hb)
      have hlmem : lowB ∈ insert newB bases := Finset.mem_insert.mpr (Or.inr hlow)
      have hnmem : newB ∈ insert newB bases := Finset.mem_insert_self _ _
      have hne_nb : newB ≠ b := fun h => hnew (h ▸ hb)
      have hL := sepN (hsep lowB hlmem b hbmem (Ne.symm hbl))
      have hN := sepN (hsep newB hnmem b hbmem hne_nb)
      exact hrb.2.2 b
        hL.1 hL.2.1 hL.2.2.1 hL.2.2.2.1 hL.2.2.2.2.1 hL.2.2.2.2.2
        hN.1 hN.2.1 hN.2.2.1 hN.2.2.2.1 hN.2.2.2.2.1 hN.2.2.2.2.2)
    hrki hgs hinj hwlow hwin

/-- One concrete tree transition: nothing changes, or a well-formed insert's
two struct writes land with separated bases. -/
def ConcreteStep (σ σ' : EVMState) (bases bases' : Finset UInt256) : Prop :=
  (σ' = σ ∧ bases' = bases)
  ∨ ∃ lowB newB ni oi v : UInt256,
      (σ.lookupAccount σ.execution_env.code_owner).isSome
      ∧ newB ∉ bases ∧ lowB ∈ bases
      ∧ (∀ b ∈ insert newB bases, ∀ c ∈ insert newB bases, b ≠ c →
          ∀ i j : UInt256, i.val < 3 → j.val < 3 → b + i ≠ c + j)
      ∧ (leafAt σ lowB).key < v
      ∧ ((leafAt σ lowB).nextKey = 0 ∨ v < (leafAt σ lowB).nextKey)
      ∧ σ' = writeLeafEvm (writeLeafEvm σ lowB (σ.sload lowB) ni v)
          newB v oi (σ.sload (lowB + 2))
      ∧ bases' = insert newB bases

/-- **CONCRETE HISTORIES ARE EVOLUTIONS.**  Along any sequence of
`ConcreteStep` transitions from a base with all invariants, every snapshot
keeps `GapSound`/`KeyInj`/`RepKeyInj`, and the represented sets form an
`Evolution` — so the abstract never-both (#34) and never-neither (#35)
theorems apply to the concrete tree directly. -/
theorem concrete_history
    {σ : ℕ → EVMState} {B : ℕ → Finset UInt256}
    (hstep : ∀ n, ConcreteStep (σ n) (σ (n+1)) (B n) (B (n+1)))
    (hgs0 : IMTAbstract.GapSound ((B 0).image (leafAt (σ 0))))
    (hinj0 : IMTAbstract.KeyInj ((B 0).image (leafAt (σ 0))))
    (hrki0 : IMTAbstract.RepKeyInj (leafAt (σ 0)) (B 0)) :
    (∀ n, IMTAbstract.GapSound ((B n).image (leafAt (σ n)))
        ∧ IMTAbstract.KeyInj ((B n).image (leafAt (σ n)))
        ∧ IMTAbstract.RepKeyInj (leafAt (σ n)) (B n))
      ∧ IMTAbstract.Evolution (fun n => (B n).image (leafAt (σ n))) := by
  have hinv : ∀ n, IMTAbstract.GapSound ((B n).image (leafAt (σ n)))
      ∧ IMTAbstract.KeyInj ((B n).image (leafAt (σ n)))
      ∧ IMTAbstract.RepKeyInj (leafAt (σ n)) (B n) := by
    intro n
    induction n with
    | zero => exact ⟨hgs0, hinj0, hrki0⟩
    | succ n ih =>
      obtain ⟨hgs, hinj, hrki⟩ := ih
      rcases hstep n with ⟨hσ, hB⟩ | ⟨lowB, newB, ni, oi, v,
          hacc, hnew, hlow, hsep, hwlow, hwin, hσ, hB⟩
      · rw [hσ, hB]
        exact ⟨hgs, hinj, hrki⟩
      · obtain ⟨_, hgs', hinj', hrki'⟩ :=
          leaves_insert_step' hacc hnew hlow hsep hrki hgs hinj hwlow hwin
        rw [hσ, hB]
        exact ⟨hgs', hinj', hrki'⟩
  refine ⟨hinv, ?_⟩
  intro n
  obtain ⟨hgs, hinj, hrki⟩ := hinv n
  rcases hstep n with ⟨hσ, hB⟩ | ⟨lowB, newB, ni, oi, v,
      hacc, hnew, hlow, hsep, hwlow, hwin, hσ, hB⟩
  · left
    simp only [hσ, hB]
  · right
    refine ⟨leafAt (σ n) lowB, v,
      Finset.mem_image.mpr ⟨lowB, hlow, rfl⟩, hwlow, hwin, ?_⟩
    obtain ⟨heff, _, _, _⟩ :=
      leaves_insert_step' hacc hnew hlow hsep hrki hgs hinj hwlow hwin
    simp only [hσ, hB]
    exact heff

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
