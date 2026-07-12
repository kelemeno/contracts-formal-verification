import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5196
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf

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

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
