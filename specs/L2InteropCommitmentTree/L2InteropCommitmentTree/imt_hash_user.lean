import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_hashLeaf
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1948431615937796266
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_5898177536972284416
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7952293271262108384
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7615139809432579602

import specs.KeccakDeterminism

/-
  IMT MERKLE HASH ATOMS — closed form for `IndexedMerkleTree`'s pair hash.

  `fun_efficientHash(lhs, rhs)` is the parent-node hash of the commitment
  tree's Merkle structure (`keccak256(lhs ‖ rhs)` via the 64-byte scratch):

      mstore(0, var_lhs); mstore(32, var_rhs); var_result := keccak256(0, 64)

  This is EXACTLY the accessor shape of `Clear.KeccakDeterminism.accOut`, so
  the pair hash inherits the whole determinism toolkit: frame-conditioned
  preimage equality, cache monotonicity/replay, and (via `accOut_replay`
  below) single-step determinism — the atom for reasoning about Merkle-path
  recomputation in the inclusion / timeout-adjacency proofs
  (`AtomicInteropProof.verifyInclusion` / `verifyTimeoutAdjacency`), which is
  the road to the finalize-XOR-refund mutual exclusion.

  Axiom-free (`[propext, Quot.sound, Classical.choice]`).
-/

namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism

set_option maxRecDepth 6000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-- `insert` on an `Ok` state writes into the underlying varstore. -/
@[simp] lemma insert_Ok {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

/-- `.evm` of a literal `Ok` state. -/
lemma evm_Ok {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

/-- Lookup through a `Finmap.insert` layer of a literal `Ok` state (skip). -/
private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok]; exact lookup_insert_of_ne h

/-- Lookup hitting the outermost `Finmap.insert` layer of a literal `Ok` state. -/
private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

/-- On an `Ok` state, `setEvm` overwrites the evm verbatim. -/
lemma evm_setEvm_of_isOk {s : State} {e : EVMState} (h : isOk s) :
    (s.setEvm e).evm = e := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

/-- `reviveJump` is the identity on `Ok` states. -/
lemma reviveJump_of_isOk {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

/-- Variable lookup is unaffected by `setEvm` (on an `Ok` state). -/
private lemma lookup_setEvm_of_isOk {s : State} {e : EVMState} {k : Identifier}
    (h : isOk s) : (s.setEvm e)[k]!! = s[k]!! := by
  obtain ⟨evm₀, st, rfl⟩ := State_of_isOk h; rfl

/-- The keccak PRIMOP in `keccakOut` form. -/
private lemma primCall_keccakOut {s : State} {a b : Literal} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (keccakOut s.evm a b).2, [(keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

/--
  Closed form of the IMT Merkle pair hash `fun_efficientHash(lhs, rhs)`:
  one `accOut` step at `(lhs, rhs)` — the returned node hash is
  `(accOut evm lhs rhs).1` and the evm advances by the keccak cache effect.
-/
lemma efficientHash_call_acc
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {lhs rhs : Literal} {v : Identifier} :
    execCall (fuel+1) fun_efficientHash [v] (Ok evm store, [lhs, rhs])
      = Ok (accOut evm lhs rhs).2 (store.insert v (accOut evm lhs rhs).1) := by
  unfold execCall call fun_efficientHash
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
  have hok₀ : isOk ((Ok evm store)☎️⟦["var_lhs", "var_rhs"], [lhs, rhs]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm₀ : ((Ok evm store)☎️⟦["var_lhs", "var_rhs"], [lhs, rhs]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hlhs : ((Ok evm store)☎️⟦["var_lhs", "var_rhs"], [lhs, rhs]⟧)["var_lhs"]!! = lhs :=
    lookup_initcall_1
  have hrhs : ((Ok evm store)☎️⟦["var_lhs", "var_rhs"], [lhs, rhs]⟧)["var_rhs"]!! = rhs :=
    lookup_initcall_2 (by decide)
  set s₀ := (Ok evm store)☎️⟦["var_lhs", "var_rhs"], [lhs, rhs]⟧ with hs₀
  set s₁ := s₀🇪⟦s₀.evm.mstore 0 (s₀["var_lhs"]!!)⟧ with hs₁
  have hs₁_ok : isOk s₁ := by rw [hs₁, isOk_setEvm]; exact hok₀
  set host := s₁🇪⟦s₁.evm.mstore 32 (s₁["var_rhs"]!!)⟧ with hhost
  have hhost_ok : isOk host := by rw [hhost, isOk_setEvm]; exact hs₁_ok
  have hhost_evm : host.evm = (evm.mstore 0 lhs).mstore 32 rhs := by
    rw [hhost, evm_setEvm_of_isOk hs₁_ok, hs₁, evm_setEvm_of_isOk hok₀, hevm₀, hlhs,
        lookup_setEvm_of_isOk hok₀, hrhs]
  rw [hhost_evm]
  unfold accOut
  generalize hout : keccakOut ((evm.mstore 0 lhs).mstore 32 rhs) 0 64 = out
  simp only [multifill_cons, multifill_nil]
  have hsetEvm_ok : isOk (host.setEvm out.2) := by
    rw [isOk_setEvm]; exact hhost_ok
  have hin_ok : isOk ((host.setEvm out.2)⟦"var_result" ↦ out.1⟧) := by
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

/-- **Pair-hash determinism (execCall level).** Two `fun_efficientHash` calls
with the same `(lhs, rhs)` return the same node hash, provided (i) the second
call's start evm agrees with the first call's end evm on the junk window
`[64, 95)`, (ii) no keccak-cache entry was dropped in between, and (iii) the
first call ended hash-collision-free.  This is the Merkle-path recomputation
atom: replaying a path over the same children provably reproduces the same
parent hashes. -/
theorem efficientHash_deterministic
    {evm₀ evmM : EVMState} {st₀ stM : VarStore} {f₁ f₂ : ℕ}
    {lhs rhs : Literal} {s₁ s₂ : State} {v₁ v₂ : Identifier}
    (h₁ : execCall (f₁+1) fun_efficientHash [v₁] (Ok evm₀ st₀, [lhs, rhs]) = s₁)
    (hmem : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i evmM.machine_state.memory
        = Finmap.lookup i s₁.evm.machine_state.memory)
    (hmono : ∀ (I : List UInt256) (w : UInt256),
      Finmap.lookup I s₁.evm.keccak_map = some w
        → Finmap.lookup I evmM.keccak_map = some w)
    (h₂ : execCall (f₂+1) fun_efficientHash [v₂] (Ok evmM stM, [lhs, rhs]) = s₂)
    (hclean : s₁.evm.hash_collision = false) :
    s₂[v₂]!! = s₁[v₁]!! := by
  rw [efficientHash_call_acc] at h₁ h₂
  have hs₁v : s₁[v₁]!! = (accOut evm₀ lhs rhs).1 := by
    rw [← h₁, ← insert_Ok]; exact lookup_insert' (by trivial)
  have hs₁evm : s₁.evm = (accOut evm₀ lhs rhs).2 := by rw [← h₁]; rfl
  have hs₂v : s₂[v₂]!! = (accOut evmM lhs rhs).1 := by
    rw [← h₂, ← insert_Ok]; exact lookup_insert' (by trivial)
  rw [hs₁evm] at hmem hmono hclean
  -- first call caches its preimage; the cache survives to the second call
  have hc : Finmap.lookup (accInterval evm₀ lhs rhs) (accOut evm₀ lhs rhs).2.keccak_map
      = some (accOut evm₀ lhs rhs).1 := accOut_caches_of_clean hclean
  have hm := hmono _ _ hc
  -- the two preimages coincide (equal args, junk windows agree)
  have hj : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i evmM.machine_state.memory
        = Finmap.lookup i evm₀.machine_state.memory := by
    intro i hi hi'
    rw [hmem i hi hi']
    exact accOut_junk_window hi
  have hI : accInterval evmM lhs rhs = accInterval evm₀ lhs rhs :=
    accInterval_eq (fun i hi hi' => by rw [hj i hi hi'])
  have h2' : accOut evmM lhs rhs = ((accOut evm₀ lhs rhs).1, (evmM.mstore 0 lhs).mstore 32 rhs) :=
    accOut_of_cached (by rw [hI]; exact hm)
  rw [hs₂v, hs₁v, h2']

/-! ## `finalize_allocation` closed form (size 128, the `hashLeaf` allocation)

`finalize_allocation(memPtr, size)` rounds `size` up to a word boundary, guards
the new free pointer against the 2⁶⁴ cap and wraparound, and bumps the free
pointer at scratch slot 64.  For the leaf-hash allocation `size = 128` the
rounding is the identity; provided the pointer arithmetic stays below the cap
(the standard well-formedness hypothesis, cf. theorem #14), the call is exactly
`mstore(64, memPtr + 128)`. -/

private lemma val_add_128 {p : UInt256} (hp : p.val + 128 ≤ 18446744073709551615) :
    ((p + (128 : UInt256))).val = p.val + 128 := by
  have h128 : ((128 : UInt256)).val = 128 := by decide
  have hlt : p.val + ((128 : UInt256)).val < UInt256.size := by
    have hs : UInt256.size = 2 ^ 256 := by norm_num
    omega
  calc ((p + (128 : UInt256))).val
      = (p.val + ((128 : UInt256)).val) % UInt256.size := rfl
    _ = p.val + ((128 : UInt256)).val := Nat.mod_eq_of_lt hlt
    _ = p.val + 128 := by rw [h128]

lemma finalize_allocation_128_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {p : Literal}
    (hp : p.val + 128 ≤ 18446744073709551615) :
    execCall (fuel+1) finalize_allocation [] (Ok evm store, [p, 128])
      = (Ok evm store).setEvm (evm.mstore 64 (p + 128)) := by
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
  set B := (Ok evm store)☎️⟦["memPtr", "size"], [p, 128]⟧ with hB
  have hokB : isOk B := isOk_initcall_of_isOk trivial
  have l_size : B["size"]!! = 128 := lookup_initcall_2 (by decide)
  have l_mem : B["memPtr"]!! = p := lookup_initcall_1
  rw [l_size]
  rw [show ((128 : UInt256) + 31) = 159 from by decide]
  set m31 := Clear.UInt256.lnot 31 with hm31
  have hok0 : isOk (B⟦"split_expr_0" ↦ 159⟧) := isOk_insert.mpr hokB
  have hok1 : isOk (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧) := isOk_insert.mpr hok0
  have l0 : (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧)["split_expr_0"]!! = 159 := by
    rw [lookup_insert_of_ne (by decide), lookup_insert' hokB]
  have l1 : (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧)["split_expr_1"]!! = m31 :=
    lookup_insert' hok0
  rw [l0, l1]
  have hland : Fin.land 159 m31 = (128 : UInt256) := by
    rw [hm31]; decide
  rw [hland]
  have l_mem2 : (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (128 : UInt256)⟧)["memPtr"]!!
      = p := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
        lookup_insert_of_ne (by decide)]
    exact l_mem
  have hok2 : isOk (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (128 : UInt256)⟧) :=
    isOk_insert.mpr hok1
  have l2 : (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (128 : UInt256)⟧)["split_expr_2"]!!
      = 128 := lookup_insert' hok1
  rw [l_mem2, l2]
  -- the two guards evaluate to 0 given `hp`
  have hMAXv : ((18446744073709551615 : UInt256)).val = 18446744073709551615 := by decide
  have hgt : fromBool (p + 128 > (18446744073709551615 : UInt256)) = (0 : UInt256) := by
    rw [decide_eq_false (by
      intro h
      rw [gt_iff_lt, Fin.lt_def, hMAXv, val_add_128 hp] at h
      omega)]
    rfl
  have hlt : fromBool (p + 128 < p) = (0 : UInt256) := by
    rw [decide_eq_false (by
      intro h
      rw [Fin.lt_def, val_add_128 hp] at h
      omega)]
    rfl
  -- resolve the newFreePtr binding, then the two guard values
  have hok3 : isOk (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (128 : UInt256)⟧⟦"newFreePtr" ↦ p + 128⟧) :=
    isOk_insert.mpr hok2
  have lnf : (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (128 : UInt256)⟧⟦"newFreePtr" ↦ p + 128⟧)["newFreePtr"]!!
      = p + 128 := lookup_insert' hok2
  rw [lnf, hgt]
  have hok4 : isOk (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (128 : UInt256)⟧⟦"newFreePtr" ↦ p + 128⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧) :=
    isOk_insert.mpr hok3
  have l3nf : (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (128 : UInt256)⟧⟦"newFreePtr" ↦ p + 128⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧)["newFreePtr"]!!
      = p + 128 := by
    rw [lookup_insert_of_ne (by decide)]; exact lnf
  have l3mem : (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (128 : UInt256)⟧⟦"newFreePtr" ↦ p + 128⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧)["memPtr"]!!
      = p := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]; exact l_mem2
  rw [l3nf, l3mem, hlt]
  -- the guard `or` is 0: skip the panic branch
  have l4a : (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (128 : UInt256)⟧⟦"newFreePtr" ↦ p + 128⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)["split_expr_3"]!!
      = 0 := by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_insert' hok3
  have l4b : (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (128 : UInt256)⟧⟦"newFreePtr" ↦ p + 128⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)["split_expr_4"]!!
      = 0 := lookup_insert' hok4
  rw [l4a, l4b]
  rw [show Fin.lor (0 : UInt256) 0 = (0 : UInt256) from by decide]
  simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  -- trailing mstore(64, newFreePtr) on the else-branch state
  have hok5 : isOk (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (128 : UInt256)⟧⟦"newFreePtr" ↦ p + 128⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧) :=
    isOk_insert.mpr hok4
  have l5nf : (B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (128 : UInt256)⟧⟦"newFreePtr" ↦ p + 128⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)["newFreePtr"]!!
      = p + 128 := by
    rw [lookup_insert_of_ne (by decide)]; exact l3nf
  rw [l5nf]
  have hBevm : B.evm = evm := by
    rw [hB]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  simp only [evm_insert, evm_Ok]
  rw [hBevm]
  have hin_ok : isOk ((B⟦"split_expr_0" ↦ 159⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (128 : UInt256)⟧⟦"newFreePtr" ↦ p + 128⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)🇪⟦evm.mstore 64 (p + 128)⟧) := by
    rw [isOk_setEvm]; exact hok5
  rw [reviveJump_of_isOk hin_ok]
  simp only [overwrite?_of_Ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = evm.mstore 64 (p + 128) := by
    have h := congrArg State.evm hi
    rw [evm_setEvm_of_isOk hok5] at h
    exact h.symm
  rw [hi, setStore_ok, hi_evm]
  rfl

/-! ## `fun_hashLeaf` closed form — the IMT leaf hash

`hashLeaf(leaf_mpos)` loads the three leaf fields `(value, nextIndex,
nextValue)` from the struct at `leaf_mpos`, abi-encodes them at the free
pointer `P = mload(64)` (fields at `P+32/P+64/P+96`, length word `96` at `P`),
finalizes the allocation (bumping the free pointer to `P+128`), and hashes the
96-byte field region: `keccak256(P+32, mload(P))`.  `leafScratchEvm` is the
evm after the five writes; the returned hash is `keccakOut` at `(P+32,
mload(P))` — the length is left as the symbolic read-back (proving
`mload(P) = 96` is the separate round-trip lemma, next). -/

/-- The evm after `hashLeaf`'s five memory writes (three fields, length word,
free-pointer bump). -/
def leafScratchEvm (evm : EVMState) (leaf : UInt256) : EVMState :=
  ((((evm.mstore (evm.mload 64 + 32) (evm.mload leaf)).mstore
      (evm.mload 64 + 64) (evm.mload (leaf + 32))).mstore
      (evm.mload 64 + 96) (evm.mload (leaf + 64))).mstore
      (evm.mload 64) 96).mstore 64 (evm.mload 64 + 128)

/-- The leaf-hash keccak step: hash the 96-byte field region at `P+32`, with
the length taken from the scratch read-back `mload(P)`. -/
def hashLeafOut (evm : EVMState) (leaf : UInt256) : UInt256 × EVMState :=
  keccakOut (leafScratchEvm evm leaf) (evm.mload 64 + 32)
    ((leafScratchEvm evm leaf).mload (evm.mload 64))

/-! The flat 16-statement replay blows up exponentially (each binding embeds
the full prior state tower), so `hashLeaf` is proven CHUNK-WISE over the four
generated Common blocks of its body, composing compact closed forms. -/

open L2InteropCommitmentTree.Common in
/-- Chunk 1 — the three field loads (pure). -/
lemma hashLeaf_chunk1
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {leaf : Literal}
    (hleaf : (Ok evm store)["var_leaf_mpos"]!! = leaf) :
    exec (fuel+1) block_1948431615937796266 (Ok evm store)
      = Ok evm (((((store.insert "_1" (evm.mload leaf)).insert
          "split_expr_0" (leaf + 32)).insert "_2" (evm.mload (leaf + 32))).insert
          "split_expr_1" (leaf + 64)).insert "_3" (evm.mload (leaf + 64))) := by
  unfold block_1948431615937796266
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', evalArgs, evalTail, cons', head',
             reverse', multifill', PrimCall', Lit', Var', execPrimCall,
             evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMload', EVMAdd']
  simp only [multifill_cons, multifill_nil]
  rw [hleaf]
  have hok0 : isOk (Ok evm store) := trivial
  have hok1 : isOk ((Ok evm store)⟦"_1" ↦ evm.mload leaf⟧) := isOk_insert.mpr hok0
  have r1 : ((Ok evm store)⟦"_1" ↦ evm.mload leaf⟧)["var_leaf_mpos"]!! = leaf := by
    rw [lookup_insert_of_ne (by decide)]; exact hleaf
  simp only [evm_insert, evm_Ok]
  rw [r1]
  have hok2 : isOk ((Ok evm store)⟦"_1" ↦ evm.mload leaf⟧⟦"split_expr_0" ↦ leaf + 32⟧) :=
    isOk_insert.mpr hok1
  have r2 : ((Ok evm store)⟦"_1" ↦ evm.mload leaf⟧⟦"split_expr_0" ↦ leaf + 32⟧)["split_expr_0"]!!
      = leaf + 32 := lookup_insert' hok1
  rw [r2]
  have hok3 : isOk ((Ok evm store)⟦"_1" ↦ evm.mload leaf⟧⟦"split_expr_0" ↦ leaf + 32⟧⟦"_2" ↦ evm.mload (leaf + 32)⟧) :=
    isOk_insert.mpr hok2
  have r3 : ((Ok evm store)⟦"_1" ↦ evm.mload leaf⟧⟦"split_expr_0" ↦ leaf + 32⟧⟦"_2" ↦ evm.mload (leaf + 32)⟧)["var_leaf_mpos"]!!
      = leaf := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]; exact r1
  rw [r3]
  have r4 : ((Ok evm store)⟦"_1" ↦ evm.mload leaf⟧⟦"split_expr_0" ↦ leaf + 32⟧⟦"_2" ↦ evm.mload (leaf + 32)⟧⟦"split_expr_1" ↦ leaf + 64⟧)["split_expr_1"]!!
      = leaf + 64 := lookup_insert' hok3
  rw [r4]
  simp only [insert_Ok]

open L2InteropCommitmentTree.Common in
/-- Chunk 2 — free pointer read and the first two field writes. -/
lemma hashLeaf_chunk2
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {a b : Literal}
    (h1 : (Ok evm store)["_1"]!! = a)
    (h2 : (Ok evm store)["_2"]!! = b) :
    exec (fuel+1) block_5898177536972284416 (Ok evm store)
      = Ok ((evm.mstore (evm.mload 64 + 32) a).mstore (evm.mload 64 + 64) b)
          (((store.insert "expr_1562_mpos" (evm.mload 64)).insert
            "_4" (evm.mload 64 + 32)).insert "split_expr_2" (evm.mload 64 + 64)) := by
  unfold block_5898177536972284416
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMload', EVMAdd', EVMMstore']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk (Ok evm store) := trivial
  have hok1 : isOk ((Ok evm store)⟦"expr_1562_mpos" ↦ evm.mload 64⟧) := isOk_insert.mpr hok0
  have r1 : ((Ok evm store)⟦"expr_1562_mpos" ↦ evm.mload 64⟧)["expr_1562_mpos"]!!
      = evm.mload 64 := lookup_insert' hok0
  simp only [evm_insert, evm_Ok]
  rw [r1]
  have hok2 : isOk ((Ok evm store)⟦"expr_1562_mpos" ↦ evm.mload 64⟧⟦"_4" ↦ evm.mload 64 + 32⟧) :=
    isOk_insert.mpr hok1
  have r2a : ((Ok evm store)⟦"expr_1562_mpos" ↦ evm.mload 64⟧⟦"_4" ↦ evm.mload 64 + 32⟧)["_4"]!!
      = evm.mload 64 + 32 := lookup_insert' hok1
  have r2b : ((Ok evm store)⟦"expr_1562_mpos" ↦ evm.mload 64⟧⟦"_4" ↦ evm.mload 64 + 32⟧)["_1"]!!
      = a := by
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]; exact h1
  rw [r2a, r2b]
  set T2 := (Ok evm store)⟦"expr_1562_mpos" ↦ evm.mload 64⟧⟦"_4" ↦ evm.mload 64 + 32⟧ with hT2
  have hok2' : isOk T2 := by rw [hT2]; exact hok2
  set E1 := evm.mstore (evm.mload 64 + 32) a with hE1
  have hokU1 : isOk (T2🇪⟦E1⟧) := by rw [isOk_setEvm]; exact hok2'
  have r3 : (T2🇪⟦E1⟧)["expr_1562_mpos"]!! = evm.mload 64 := by
    rw [lookup_setEvm_of_isOk hok2', hT2, lookup_insert_of_ne (by decide)]
    exact r1
  rw [r3]
  have hokU2 : isOk ((T2🇪⟦E1⟧)⟦"split_expr_2" ↦ evm.mload 64 + 64⟧) := isOk_insert.mpr hokU1
  have r4a : ((T2🇪⟦E1⟧)⟦"split_expr_2" ↦ evm.mload 64 + 64⟧)["split_expr_2"]!!
      = evm.mload 64 + 64 := lookup_insert' hokU1
  have r4b : ((T2🇪⟦E1⟧)⟦"split_expr_2" ↦ evm.mload 64 + 64⟧)["_2"]!! = b := by
    rw [lookup_insert_of_ne (by decide), lookup_setEvm_of_isOk hok2', hT2,
        lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact h2
  have r4c : (T2🇪⟦E1⟧).evm = E1 := evm_setEvm_of_isOk hok2'
  rw [r4a, r4b, r4c]
  -- collapse the state: Ok-with-setEvm-and-inserts to the literal Ok form
  rw [hT2, hE1]
  rfl

open L2InteropCommitmentTree.Common in
/-- Chunk 3 — third field write, length word, allocation finalize, length
read-back (kept symbolic). -/
lemma hashLeaf_chunk3
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {P c : Literal}
    (hP : (Ok evm store)["expr_1562_mpos"]!! = P)
    (h3 : (Ok evm store)["_3"]!! = c)
    (hp128 : P.val + 128 ≤ 18446744073709551615) :
    exec (fuel+1) block_7952293271262108384 (Ok evm store)
      = Ok ((((evm.mstore (P + 96) c).mstore P 96).mstore 64 (P + 128)))
          ((store.insert "split_expr_3" (P + 96)).insert "split_expr_4"
            ((((evm.mstore (P + 96) c).mstore P 96).mstore 64 (P + 128)).mload P)) := by
  unfold block_7952293271262108384
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall', LetCall', ExprStmtCall',
             evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMload', EVMAdd', EVMMstore']
  simp only [multifill_cons, multifill_nil]
  rw [hP]
  have hok0 : isOk (Ok evm store) := trivial
  have hok1 : isOk ((Ok evm store)⟦"split_expr_3" ↦ P + 96⟧) := isOk_insert.mpr hok0
  have r1a : ((Ok evm store)⟦"split_expr_3" ↦ P + 96⟧)["split_expr_3"]!! = P + 96 :=
    lookup_insert' hok0
  have r1b : ((Ok evm store)⟦"split_expr_3" ↦ P + 96⟧)["_3"]!! = c := by
    rw [lookup_insert_of_ne (by decide)]; exact h3
  simp only [evm_insert, evm_Ok]
  rw [r1a, r1b]
  set T1 := (Ok evm store)⟦"split_expr_3" ↦ P + 96⟧ with hT1
  have hok1' : isOk T1 := by rw [hT1]; exact hok1
  set E3 := evm.mstore (P + 96) c with hE3
  have hokU1 : isOk (T1🇪⟦E3⟧) := by rw [isOk_setEvm]; exact hok1'
  have r2a : (T1🇪⟦E3⟧)["expr_1562_mpos"]!! = P := by
    rw [lookup_setEvm_of_isOk hok1', hT1, lookup_insert_of_ne (by decide)]
    exact hP
  have r2b : (T1🇪⟦E3⟧).evm = E3 := evm_setEvm_of_isOk hok1'
  rw [r2a, r2b]
  set E4 := E3.mstore P 96 with hE4
  have hokU2 : isOk ((T1🇪⟦E3⟧)🇪⟦E4⟧) := by rw [isOk_setEvm, isOk_setEvm]; exact hok1'
  have r3 : ((T1🇪⟦E3⟧)🇪⟦E4⟧)["expr_1562_mpos"]!! = P := by
    rw [lookup_setEvm_of_isOk (by rw [isOk_setEvm]; exact hok1')]
    exact r2a
  rw [r3]
  obtain ⟨e6, σ6, h6⟩ := State_of_isOk hokU2
  have he6 : e6 = E4 := by
    have h := congrArg State.evm h6
    rw [evm_setEvm_of_isOk (by rw [isOk_setEvm]; exact hok1')] at h
    exact h.symm
  have r3' : (Ok e6 σ6)["expr_1562_mpos"]!! = P := by rw [← h6]; exact r3
  rw [h6, finalize_allocation_128_call hp128]
  have hokW : isOk ((Ok e6 σ6).setEvm (e6.mstore 64 (P + 128))) := by
    rw [isOk_setEvm]; trivial
  have r4 : ((Ok e6 σ6).setEvm (e6.mstore 64 (P + 128)))["expr_1562_mpos"]!! = P := by
    rw [lookup_setEvm_of_isOk (by trivial)]; exact r3'
  have r4b : ((Ok e6 σ6).setEvm (e6.mstore 64 (P + 128))).evm = e6.mstore 64 (P + 128) :=
    evm_setEvm_of_isOk (by trivial)
  rw [r4, r4b]
  -- collapse to the literal Ok form; recover σ6's shape from h6
  have hσ6 : σ6 = store.insert "split_expr_3" (P + 96) := by
    have h := congrArg (fun s => match s with | Ok _ σ => σ | _ => σ6) h6
    simp only at h
    rw [hT1] at h
    exact h.symm
  rw [he6, hσ6, hE4, hE3]
  rfl

open L2InteropCommitmentTree.Common in
/-- Chunk 4 — the leaf-hash keccak itself. -/
lemma hashLeaf_chunk4
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x l : Literal}
    (hx : (Ok evm store)["_4"]!! = x)
    (hl : (Ok evm store)["split_expr_4"]!! = l) :
    exec (fuel+1) block_7615139809432579602 (Ok evm store)
      = Ok (keccakOut evm x l).2 (store.insert "var" (keccakOut evm x l).1) := by
  unfold block_7615139809432579602
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', evalArgs, evalTail, cons', head',
             reverse', multifill', PrimCall', Lit', Var', execPrimCall,
             evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append]
  rw [primCall_keccakOut, hx, hl]
  simp only [multifill_cons, multifill_nil]
  rfl

set_option maxHeartbeats 8000000 in
open L2InteropCommitmentTree.Common in
/-- **`fun_hashLeaf` closed form** — composed from the four chunk lemmas. -/
lemma hashLeaf_call_acc
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {leaf : Literal} {v : Identifier}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615) :
    execCall (fuel+1) fun_hashLeaf [v] (Ok evm store, [leaf])
      = Ok (hashLeafOut evm leaf).2 (store.insert v (hashLeafOut evm leaf).1) := by
  have hbody : fun_hashLeaf.body
      = [block_1948431615937796266, block_5898177536972284416,
         block_7952293271262108384, block_7615139809432579602] := by
    rfl
  have hparams : fun_hashLeaf.params = ["var_leaf_mpos"] := rfl
  have hrets : fun_hashLeaf.rets = ["var"] := rfl
  unfold execCall call
  simp only [hparams, hrets, hbody]
  simp only [multifill', mkOk_initcall_Ok, List.map_nil, List.map_cons]
  rw [cons, cons, cons, cons, nil]
  -- expose the initcall state as a literal `Ok`
  have hok0 : isOk ((Ok evm store)☎️⟦["var_leaf_mpos"], [leaf]⟧) := isOk_initcall_of_isOk trivial
  obtain ⟨e0, σ0, h0⟩ := State_of_isOk hok0
  have hleaf0 : ((Ok evm store)☎️⟦["var_leaf_mpos"], [leaf]⟧)["var_leaf_mpos"]!! = leaf :=
    lookup_initcall_1
  have he0 : e0 = evm := by
    have h := congrArg State.evm h0
    rw [show ((Ok evm store)☎️⟦["var_leaf_mpos"], [leaf]⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at h
    exact h.symm
  rw [h0, he0] at hleaf0
  simp only [h0, he0]
  -- chunk 1
  simp only [hashLeaf_chunk1 hleaf0]
  -- chunk 2
  have h1 : (Ok evm (((((σ0.insert "_1" (evm.mload leaf)).insert
      "split_expr_0" (leaf + 32)).insert "_2" (evm.mload (leaf + 32))).insert
      "split_expr_1" (leaf + 64)).insert "_3" (evm.mload (leaf + 64))))["_1"]!!
      = evm.mload leaf := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  have h2 : (Ok evm (((((σ0.insert "_1" (evm.mload leaf)).insert
      "split_expr_0" (leaf + 32)).insert "_2" (evm.mload (leaf + 32))).insert
      "split_expr_1" (leaf + 64)).insert "_3" (evm.mload (leaf + 64))))["_2"]!!
      = evm.mload (leaf + 32) := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  simp only [hashLeaf_chunk2 h1 h2]
  -- chunk 3 (the store from chunk 2, evm advanced by the two writes)
  set σ2 := ((((((σ0.insert "_1" (evm.mload leaf)).insert
      "split_expr_0" (leaf + 32)).insert "_2" (evm.mload (leaf + 32))).insert
      "split_expr_1" (leaf + 64)).insert "_3" (evm.mload (leaf + 64))).insert
      "expr_1562_mpos" (evm.mload 64)).insert "_4" (evm.mload 64 + 32) with hσ2
  set E2 := (evm.mstore (evm.mload 64 + 32) (evm.mload leaf)).mstore (evm.mload 64 + 64)
      (evm.mload (leaf + 32)) with hE2
  have hP : (Ok E2 (σ2.insert "split_expr_2" (evm.mload 64 + 64)))["expr_1562_mpos"]!!
      = evm.mload 64 := by
    rw [lookup_insert_ne_fin (by decide), hσ2,
        lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  have h3 : (Ok E2 (σ2.insert "split_expr_2" (evm.mload 64 + 64)))["_3"]!!
      = evm.mload (leaf + 64) := by
    rw [lookup_insert_ne_fin (by decide), hσ2,
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  simp only [hashLeaf_chunk3 hP h3 hp]
  -- chunk 4
  set E5 := ((E2.mstore (evm.mload 64 + 96) (evm.mload (leaf + 64))).mstore
      (evm.mload 64) 96).mstore 64 (evm.mload 64 + 128) with hE5
  set σ3 := ((σ2.insert "split_expr_2" (evm.mload 64 + 64)).insert
      "split_expr_3" (evm.mload 64 + 96)).insert "split_expr_4" (E5.mload (evm.mload 64)) with hσ3
  have hx : (Ok E5 σ3)["_4"]!! = evm.mload 64 + 32 := by
    rw [hσ3, lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), hσ2]
    exact lookup_insert_self_fin
  have hl : (Ok E5 σ3)["split_expr_4"]!! = E5.mload (evm.mload 64) := by
    rw [hσ3]
    exact lookup_insert_self_fin
  simp only [hashLeaf_chunk4 hx hl]
  -- rets lookup + call wrappers
  have hokF : isOk (Ok (keccakOut E5 (evm.mload 64 + 32) (E5.mload (evm.mload 64))).2
      (σ3.insert "var" (keccakOut E5 (evm.mload 64 + 32) (E5.mload (evm.mload 64))).1)) := trivial
  have hvar : (Ok (keccakOut E5 (evm.mload 64 + 32) (E5.mload (evm.mload 64))).2
      (σ3.insert "var" (keccakOut E5 (evm.mload 64 + 32) (E5.mload (evm.mload 64))).1))["var"]!!
      = (keccakOut E5 (evm.mload 64 + 32) (E5.mload (evm.mload 64))).1 :=
    lookup_insert_self_fin
  simp only [hvar]
  rw [reviveJump_of_isOk hokF]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [multifill_cons, multifill_nil, insert_Ok]
  -- align with `hashLeafOut`
  have halign : keccakOut E5 (evm.mload 64 + 32) (E5.mload (evm.mload 64))
      = hashLeafOut evm leaf := by
    rw [hE5, hE2]
    unfold hashLeafOut leafScratchEvm
    rfl
  rw [halign]

/-- **Length read-back.** On the leaf scratch, `mload(P)` returns the length
word `96` that `hashLeaf` wrote at the free pointer: the free-pointer bump at
`64` cannot touch `[P, P+32)` when `96 ≤ P` (true of any real free pointer,
which starts at `0x80`), and the write at `P` round-trips. -/
lemma leafScratch_length_readback
    {evm : EVMState} {leaf : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    (leafScratchEvm evm leaf).mload (evm.mload 64) = 96 := by
  have hms : (leafScratchEvm evm leaf).machine_state
      = ((((evm.machine_state.updateMemory (evm.mload 64 + 32) (evm.mload leaf)).updateMemory
          (evm.mload 64 + 64) (evm.mload (leaf + 32))).updateMemory
          (evm.mload 64 + 96) (evm.mload (leaf + 64))).updateMemory
          (evm.mload 64) 96).updateMemory 64 (evm.mload 64 + 128) := rfl
  show (leafScratchEvm evm leaf).machine_state.lookupMemory (evm.mload 64) = 96
  rw [hms]
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have h64v : ((64 : UInt256)).val = 64 := by decide
  rw [lookupMemory_updateMemory_outside _ 64 (evm.mload 64 + 128) (evm.mload 64)
      (by rw [h64v]; norm_num)
      (by omega)
      (by right; rw [h64v]; omega)]
  exact lookupMemory_updateMemory_self' _ (evm.mload 64) 96 (by omega)

/-- The leaf hash with the length resolved: `hashLeaf` hashes exactly the
96-byte field region `[P+32, P+128)` of the scratch. -/
lemma hashLeafOut_length
    {evm : EVMState} {leaf : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    hashLeafOut evm leaf
      = keccakOut (leafScratchEvm evm leaf) (evm.mload 64 + 32) 96 := by
  unfold hashLeafOut
  rw [leafScratch_length_readback hp hplow]

private lemma val_add_lit {P q : UInt256} {c : ℕ} (hq : q.val = c)
    (hbound : P.val + c < 2 ^ 256) : (P + q).val = P.val + c := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  rw [Fin.val_add, hq]
  exact Nat.mod_eq_of_lt (by omega)

/-- **Scratch byte agreement.** Two leaf scratches built over the same free
pointer and the same three field values agree on every byte of the hash-
relevant range `[P+32, P+159)`, provided the underlying memories agree on the
junk tail `[P+128, P+159)`: bytes of `[P+32, P+128)` come from the (equal)
field writes; the tail is untouched by all five writes. -/
lemma leafScratch_byte_agree
    {σ₁ σ₂ : EVMState} {leaf₁ leaf₂ : Literal}
    (hP : σ₂.mload 64 = σ₁.mload 64)
    (ha : σ₂.mload leaf₂ = σ₁.mload leaf₁)
    (hb : σ₂.mload (leaf₂ + 32) = σ₁.mload (leaf₁ + 32))
    (hc : σ₂.mload (leaf₂ + 64) = σ₁.mload (leaf₁ + 64))
    (hp : (σ₁.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (σ₁.mload 64).val)
    (hjunk : ∀ i : UInt256, (σ₁.mload 64).val + 128 ≤ i.val →
        i.val < (σ₁.mload 64).val + 159 →
      Finmap.lookup i σ₂.machine_state.memory = Finmap.lookup i σ₁.machine_state.memory) :
    ∀ i : UInt256, (σ₁.mload 64).val + 32 ≤ i.val → i.val < (σ₁.mload 64).val + 159 →
      Finmap.lookup i (leafScratchEvm σ₂ leaf₂).machine_state.memory
        = Finmap.lookup i (leafScratchEvm σ₁ leaf₁).machine_state.memory := by
  intro i hlo hhi
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have h32v : ((32 : UInt256)).val = 32 := by decide
  have h96v : ((96 : UInt256)).val = 96 := by decide
  set P := σ₁.mload 64 with hPdef
  have hP32 : (P + 32).val = P.val + 32 := val_add_lit h32v (by omega)
  have hP64 : (P + 64).val = P.val + 64 := val_add_lit h64v (by omega)
  have hP96 : (P + 96).val = P.val + 96 := val_add_lit h96v (by omega)
  have hms₂ : (leafScratchEvm σ₂ leaf₂).machine_state
      = ((((σ₂.machine_state.updateMemory (P + 32) (σ₁.mload leaf₁)).updateMemory
          (P + 64) (σ₁.mload (leaf₁ + 32))).updateMemory
          (P + 96) (σ₁.mload (leaf₁ + 64))).updateMemory
          P 96).updateMemory 64 (P + 128) := by
    show ((((σ₂.machine_state.updateMemory (σ₂.mload 64 + 32) (σ₂.mload leaf₂)).updateMemory
          (σ₂.mload 64 + 64) (σ₂.mload (leaf₂ + 32))).updateMemory
          (σ₂.mload 64 + 96) (σ₂.mload (leaf₂ + 64))).updateMemory
          (σ₂.mload 64) 96).updateMemory 64 (σ₂.mload 64 + 128) = _
    rw [hP, ha, hb, hc]
  have hms₁ : (leafScratchEvm σ₁ leaf₁).machine_state
      = ((((σ₁.machine_state.updateMemory (P + 32) (σ₁.mload leaf₁)).updateMemory
          (P + 64) (σ₁.mload (leaf₁ + 32))).updateMemory
          (P + 96) (σ₁.mload (leaf₁ + 64))).updateMemory
          P 96).updateMemory 64 (P + 128) := rfl
  rw [hms₁, hms₂]
  -- write 5 (free-pointer bump at 64) never reaches [P+32, P+159)
  rw [lookup_updateMemory_outside_val _ 64 (P + 128) i (by rw [h64v]; norm_num)
      (by right; rw [h64v]; omega),
      lookup_updateMemory_outside_val _ 64 (P + 128) i (by rw [h64v]; norm_num)
      (by right; rw [h64v]; omega)]
  -- write 4 (length word at P) never reaches [P+32, …)
  rw [lookup_updateMemory_outside_val _ P 96 i (by omega) (by right; omega),
      lookup_updateMemory_outside_val _ P 96 i (by omega) (by right; omega)]
  rcases Nat.lt_or_ge i.val (P.val + 64) with hA | hBc
  · -- field 1 window [P+32, P+64)
    rw [lookup_updateMemory_outside_val _ (P + 96) _ i (by rw [hP96]; omega)
        (by left; rw [hP96]; omega),
        lookup_updateMemory_outside_val _ (P + 96) _ i (by rw [hP96]; omega)
        (by left; rw [hP96]; omega)]
    rw [lookup_updateMemory_outside_val _ (P + 64) _ i (by rw [hP64]; omega)
        (by left; rw [hP64]; omega),
        lookup_updateMemory_outside_val _ (P + 64) _ i (by rw [hP64]; omega)
        (by left; rw [hP64]; omega)]
    have hi_form : i = (↑(i.val - (P.val + 32)) : UInt256) + (P + 32) := by
      apply Fin.ext
      rw [Fin.val_add, hP32, Fin.val_cast_of_lt (by omega)]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hi_form,
        lookup_updateMemory_at _ (P + 32) _ (i.val - (P.val + 32)) (by omega)
          (window_nodup (P + 32) (by rw [hP32]; omega)),
        lookup_updateMemory_at _ (P + 32) _ (i.val - (P.val + 32)) (by omega)
          (window_nodup (P + 32) (by rw [hP32]; omega))]
  · rcases Nat.lt_or_ge i.val (P.val + 96) with hB | hCd
    · -- field 2 window [P+64, P+96)
      rw [lookup_updateMemory_outside_val _ (P + 96) _ i (by rw [hP96]; omega)
          (by left; rw [hP96]; omega),
          lookup_updateMemory_outside_val _ (P + 96) _ i (by rw [hP96]; omega)
          (by left; rw [hP96]; omega)]
      have hi_form : i = (↑(i.val - (P.val + 64)) : UInt256) + (P + 64) := by
        apply Fin.ext
        rw [Fin.val_add, hP64, Fin.val_cast_of_lt (by omega)]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hi_form,
          lookup_updateMemory_at _ (P + 64) _ (i.val - (P.val + 64)) (by omega)
            (window_nodup (P + 64) (by rw [hP64]; omega)),
          lookup_updateMemory_at _ (P + 64) _ (i.val - (P.val + 64)) (by omega)
            (window_nodup (P + 64) (by rw [hP64]; omega))]
    · rcases Nat.lt_or_ge i.val (P.val + 128) with hC | hD
      · -- field 3 window [P+96, P+128)
        have hi_form : i = (↑(i.val - (P.val + 96)) : UInt256) + (P + 96) := by
          apply Fin.ext
          rw [Fin.val_add, hP96, Fin.val_cast_of_lt (by omega)]
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        rw [hi_form,
            lookup_updateMemory_at _ (P + 96) _ (i.val - (P.val + 96)) (by omega)
              (window_nodup (P + 96) (by rw [hP96]; omega)),
            lookup_updateMemory_at _ (P + 96) _ (i.val - (P.val + 96)) (by omega)
              (window_nodup (P + 96) (by rw [hP96]; omega))]
      · -- junk tail [P+128, P+159): outside all field windows on both sides
        rw [lookup_updateMemory_outside_val _ (P + 96) _ i (by rw [hP96]; omega)
            (by right; rw [hP96]; omega),
            lookup_updateMemory_outside_val _ (P + 96) _ i (by rw [hP96]; omega)
            (by right; rw [hP96]; omega)]
        rw [lookup_updateMemory_outside_val _ (P + 64) _ i (by rw [hP64]; omega)
            (by right; rw [hP64]; omega),
            lookup_updateMemory_outside_val _ (P + 64) _ i (by rw [hP64]; omega)
            (by right; rw [hP64]; omega)]
        rw [lookup_updateMemory_outside_val _ (P + 32) _ i (by rw [hP32]; omega)
            (by right; rw [hP32]; omega),
            lookup_updateMemory_outside_val _ (P + 32) _ i (by rw [hP32]; omega)
            (by right; rw [hP32]; omega)]
        exact hjunk i (by omega) (by omega)

/-- **Leaf-hash determinism.** Two `hashLeaf` computations over the same free
pointer, the same three field values, agreeing junk tail, surviving cache, and
a collision-free first run produce the SAME leaf hash. -/
theorem hashLeafOut_deterministic
    {σ₁ σ₂ : EVMState} {leaf₁ leaf₂ : Literal}
    (hP : σ₂.mload 64 = σ₁.mload 64)
    (ha : σ₂.mload leaf₂ = σ₁.mload leaf₁)
    (hb : σ₂.mload (leaf₂ + 32) = σ₁.mload (leaf₁ + 32))
    (hc : σ₂.mload (leaf₂ + 64) = σ₁.mload (leaf₁ + 64))
    (hp : (σ₁.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (σ₁.mload 64).val)
    (hjunk : ∀ i : UInt256, (σ₁.mload 64).val + 128 ≤ i.val →
        i.val < (σ₁.mload 64).val + 159 →
      Finmap.lookup i σ₂.machine_state.memory = Finmap.lookup i σ₁.machine_state.memory)
    (hmono : ∀ (I : List UInt256) (w : UInt256),
      Finmap.lookup I (hashLeafOut σ₁ leaf₁).2.keccak_map = some w →
        Finmap.lookup I σ₂.keccak_map = some w)
    (hclean : (hashLeafOut σ₁ leaf₁).2.hash_collision = false) :
    (hashLeafOut σ₂ leaf₂).1 = (hashLeafOut σ₁ leaf₁).1 := by
  have hp₂ : (σ₂.mload 64).val + 128 ≤ 18446744073709551615 := by rw [hP]; exact hp
  have hplow₂ : 96 ≤ (σ₂.mload 64).val := by rw [hP]; exact hplow
  rw [hashLeafOut_length hp₂ hplow₂, hashLeafOut_length hp hplow] at *
  rw [hP]
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have h32v : ((32 : UInt256)).val = 32 := by decide
  have h96v : ((96 : UInt256)).val = 96 := by decide
  have hP32 : (σ₁.mload 64 + 32).val = (σ₁.mload 64).val + 32 :=
    val_add_lit h32v (by omega)
  apply keccakOut_deterministic
  · -- equal 96-byte preimages
    apply mkInterval_eq_of_byte_agree (by rw [hP32, h96v]; omega)
    intro i hi hi'
    rw [hP32] at hi
    rw [hP32, h96v] at hi'
    exact leafScratch_byte_agree hP ha hb hc hp hplow hjunk i (by omega) (by omega)
  · -- the cache survives (mstores do not touch the keccak map)
    intro I w hIw
    have : Finmap.lookup I σ₂.keccak_map = some w := hmono I w hIw
    exact this
  · exact hclean

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
