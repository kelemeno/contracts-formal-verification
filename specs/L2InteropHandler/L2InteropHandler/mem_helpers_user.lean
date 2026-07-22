import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import generated.L2InteropHandler.L2InteropHandler.checked_sub_uint256
import generated.L2InteropHandler.L2InteropHandler.array_allocation_size_bytes
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation
import generated.L2InteropHandler.L2InteropHandler.mcopy

/-
  MEMORY/ARITHMETIC HELPER CLOSED FORMS (L2InteropHandler).

  The two small pure helpers on `fun_slice`'s dependency path (and used
  corpus-wide), driven to `execCall` closed forms in their non-panicking
  directions:

  * `checked_sub_call`        — `checked_sub_uint256`: without underflow the
    call returns `x - y` (panic `0x11` otherwise);
  * `array_alloc_bytes_call`  — `array_allocation_size_bytes`: for a length
    within the 64-bit bound the call returns the padded allocation size
    `((length + 31) &&& ~31) + 32` (panic `0x41` otherwise).

  Both evm-pure.  Axiom-free.
-/

namespace generated.L2InteropHandler.L2InteropHandler

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

private lemma reviveJump_of_isOk {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

/-! ### `checked_sub_uint256` -/

/-- **Checked subtraction, no underflow**: the call returns `x - y`,
evm untouched. -/
lemma checked_sub_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {x y : Literal}
    {d : Identifier}
    (hle : ¬ (x - y > x)) :
    execCall (fuel+1) checked_sub_uint256 [d] (Ok evm store, [x, y])
      = Ok evm (store.insert d (x - y)) := by
  unfold execCall call checked_sub_uint256
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  have hok0 : isOk ((Ok evm store)☎️⟦["x", "y"], [x, y]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["x", "y"], [x, y]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  set J := (Ok evm store)☎️⟦["x", "y"], [x, y]⟧
  -- diff := sub(x, y)
  rw [cons, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMSub']
  rw [show J["x"]!! = x from lookup_initcall_1]
  rw [show J["y"]!! = y from by exact lookup_initcall_2 (by decide)]
  -- if gt(diff, x) — skip
  rw [cons, nil, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMGt']
  have hok1 : isOk (J⟦"diff" ↦ x - y⟧) := by
    rw [isOk_insert]; exact hok0
  rw [show (J⟦"diff" ↦ x - y⟧)["diff"]!! = x - y from lookup_insert' hok0]
  rw [show (J⟦"diff" ↦ x - y⟧)["x"]!! = x from by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_initcall_1]
  rw [show fromBool (x - y > x) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hle, if_false]]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- the ret lookup and the wrapper
  rw [show (J⟦"diff" ↦ x - y⟧)["diff"]!! = x - y from lookup_insert' hok0]
  obtain ⟨e1, σ1, h1⟩ := State_of_isOk hok1
  have he1 : e1 = evm := by
    have h := congrArg State.evm h1
    rw [evm_insert, hevm0] at h
    exact h.symm
  rw [h1]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [insert_Ok]
  rw [he1]

/-! ### `array_allocation_size_bytes` -/

/-- **Byte-array allocation size, in bound**: for `length ≤ 2^64 - 1` the call
returns the word-padded size `((length + 31) &&& ~31) + 32`, evm untouched. -/
lemma array_alloc_bytes_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {L : Literal}
    {sz : Identifier}
    (hL : ¬ (L > (18446744073709551615 : UInt256))) :
    execCall (fuel+1) array_allocation_size_bytes [sz] (Ok evm store, [L])
      = Ok evm (store.insert sz
          (Fin.land (L + 31) (Clear.UInt256.lnot 31) + 32)) := by
  unfold execCall call array_allocation_size_bytes
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  have hok0 : isOk ((Ok evm store)☎️⟦["length"], [L]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["length"], [L]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  set J := (Ok evm store)☎️⟦["length"], [L]⟧
  -- if gt(length, 2^64 - 1) — skip
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMGt']
  rw [show J["length"]!! = L from lookup_initcall_1]
  rw [show fromBool (L > (18446744073709551615 : UInt256)) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hL, if_false]]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- let split_expr_1 := add(length, 31)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd']
  rw [show J["length"]!! = L from lookup_initcall_1]
  -- let split_expr_2 := not(31)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMNot']
  -- let split_expr_3 := and(split_expr_1, split_expr_2)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAnd']
  have hok1 : isOk (J⟦"split_expr_1" ↦ L + 31⟧) := by
    rw [isOk_insert]; exact hok0
  have hok2 : isOk (J⟦"split_expr_1" ↦ L + 31⟧⟦"split_expr_2" ↦ Clear.UInt256.lnot 31⟧) := by
    rw [isOk_insert]; exact hok1
  rw [show (J⟦"split_expr_1" ↦ L + 31⟧⟦"split_expr_2" ↦ Clear.UInt256.lnot 31⟧)["split_expr_1"]!! = L + 31 from by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_insert' hok0]
  rw [show (J⟦"split_expr_1" ↦ L + 31⟧⟦"split_expr_2" ↦ Clear.UInt256.lnot 31⟧)["split_expr_2"]!! = Clear.UInt256.lnot 31 from
    lookup_insert' hok1]
  -- size := add(split_expr_3, 32)
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd']
  have hok3 : isOk (J⟦"split_expr_1" ↦ L + 31⟧⟦"split_expr_2" ↦ Clear.UInt256.lnot 31⟧⟦"split_expr_3" ↦ Fin.land (L + 31) (Clear.UInt256.lnot 31)⟧) := by
    rw [isOk_insert]; exact hok2
  rw [show (J⟦"split_expr_1" ↦ L + 31⟧⟦"split_expr_2" ↦ Clear.UInt256.lnot 31⟧⟦"split_expr_3" ↦ Fin.land (L + 31) (Clear.UInt256.lnot 31)⟧)["split_expr_3"]!! = Fin.land (L + 31) (Clear.UInt256.lnot 31) from
    lookup_insert' hok2]
  -- the ret lookup and the wrapper
  have hok4 : isOk (J⟦"split_expr_1" ↦ L + 31⟧⟦"split_expr_2" ↦ Clear.UInt256.lnot 31⟧⟦"split_expr_3" ↦ Fin.land (L + 31) (Clear.UInt256.lnot 31)⟧⟦"size" ↦ Fin.land (L + 31) (Clear.UInt256.lnot 31) + 32⟧) := by
    rw [isOk_insert]; exact hok3
  rw [show (J⟦"split_expr_1" ↦ L + 31⟧⟦"split_expr_2" ↦ Clear.UInt256.lnot 31⟧⟦"split_expr_3" ↦ Fin.land (L + 31) (Clear.UInt256.lnot 31)⟧⟦"size" ↦ Fin.land (L + 31) (Clear.UInt256.lnot 31) + 32⟧)["size"]!! = Fin.land (L + 31) (Clear.UInt256.lnot 31) + 32 from
    lookup_insert' hok3]
  obtain ⟨e4, σ4, h4⟩ := State_of_isOk hok4
  have he4 : e4 = evm := by
    have h := congrArg State.evm h4
    rw [evm_insert, evm_insert, evm_insert, evm_insert, hevm0] at h
    exact h.symm
  rw [h4]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [insert_Ok]
  rw [he4]

/-! ### `finalize_allocation` (generic) — arm lemmas per generated chunk -/

/-- Chunk 1 of the generated body: pad the size, compute the new free pointer,
evaluate the overflow flag. -/
@[reducible] private def finChunk1 : Stmt := <s
  {
      let split_expr_0 := add(size, 31)
      let split_expr_1 := not(31)
      let split_expr_2 := and(split_expr_0, split_expr_1)
      let newFreePtr := add(memPtr, split_expr_2)
      let split_expr_3 := gt(newFreePtr, 18446744073709551615)
  }
>

/-- Chunk 2: evaluate the wrap flag. -/
@[reducible] private def finChunk2 : Stmt := <s
  {
      let split_expr_4 := lt(newFreePtr, memPtr)
  }
>

private lemma finChunk1_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {P Z : Literal}
    (hP : (Ok evm σ)["memPtr"]!! = P)
    (hZ : (Ok evm σ)["size"]!! = Z)
    (h1 : ¬ (P + Fin.land (Z + 31) (Clear.UInt256.lnot 31)
      > (18446744073709551615 : UInt256))) :
    exec (fuel+1) finChunk1 (Ok evm σ)
      = Ok evm (((((σ.insert "split_expr_0" (Z + 31)).insert
          "split_expr_1" (Clear.UInt256.lnot 31)).insert
          "split_expr_2" (Fin.land (Z + 31) (Clear.UInt256.lnot 31))).insert
          "newFreePtr" (P + Fin.land (Z + 31) (Clear.UInt256.lnot 31))).insert
          "split_expr_3" 0) := by
  unfold finChunk1
  -- let split_expr_0 := add(size, 31)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [hZ]
  -- let split_expr_1 := not(31)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMNot',
             insert_Ok]
  -- let split_expr_2 := and(split_expr_0, split_expr_1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAnd',
             insert_Ok]
  rw [lookup_insert_self_fin, lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  -- let newFreePtr := add(memPtr, split_expr_2)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_self_fin, lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hP]
  -- let split_expr_3 := gt(newFreePtr, MAX)
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMGt',
             insert_Ok]
  rw [lookup_insert_self_fin]
  rw [show fromBool (P + Fin.land (Z + 31) (Clear.UInt256.lnot 31)
        > (18446744073709551615 : UInt256)) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false h1, if_false]]

private lemma finChunk2_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {N P : Literal}
    (hN : (Ok evm σ)["newFreePtr"]!! = N)
    (hP : (Ok evm σ)["memPtr"]!! = P)
    (h2 : ¬ (N < P)) :
    exec (fuel+1) finChunk2 (Ok evm σ)
      = Ok evm (σ.insert "split_expr_4" 0) := by
  unfold finChunk2
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMLt',
             insert_Ok]
  rw [hN, hP]
  rw [show fromBool (N < P) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false h2, if_false]]

/-- **Generic `finalize_allocation`, non-panicking direction**: without
overflow or wrap the call bumps the free-memory pointer to
`memPtr + ((size + 31) &&& ~31)` and returns nothing else. -/
lemma finalize_alloc_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {P Z : Literal}
    (h1 : ¬ (P + Fin.land (Z + 31) (Clear.UInt256.lnot 31)
      > (18446744073709551615 : UInt256)))
    (h2 : ¬ (P + Fin.land (Z + 31) (Clear.UInt256.lnot 31) < P)) :
    execCall (fuel+1) finalize_allocation [] (Ok evm store, [P, Z])
      = Ok (evm.mstore 64 (P + Fin.land (Z + 31) (Clear.UInt256.lnot 31)))
          store := by
  unfold execCall call finalize_allocation
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  have hok0 : isOk ((Ok evm store)☎️⟦["memPtr", "size"], [P, Z]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["memPtr", "size"], [P, Z]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  set J := (Ok evm store)☎️⟦["memPtr", "size"], [P, Z]⟧
  obtain ⟨e0, σ0, hJ0⟩ := State_of_isOk hok0
  have he0 : e0 = evm := by
    have h := congrArg State.evm hJ0
    rw [hevm0] at h
    exact h.symm
  subst he0
  rw [hJ0]
  -- chunk 1
  rw [cons]
  rw [finChunk1_arm (P := P) (Z := Z)
    (by rw [← hJ0]; exact lookup_initcall_1)
    (by rw [← hJ0]; exact lookup_initcall_2 (by decide))
    h1]
  -- chunk 2
  rw [cons]
  rw [finChunk2_arm (N := P + Fin.land (Z + 31) (Clear.UInt256.lnot 31)) (P := P)
    (by rw [lookup_insert_ne_fin (by decide)]; exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        rw [← hJ0]; exact lookup_initcall_1)
    h2]
  -- if or(split_expr_3, split_expr_4) — skip
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMOr']
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [show Fin.lor (0 : UInt256) 0 = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- mstore(64, newFreePtr)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  -- wrapper
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]

/-! ### The clamp switch (generic) and the `mcopy` call -/

/-- The min/max-clamp switch shape shared by `fun_slice`'s two bound clamps:
`switch lt(a, b) case 0 { t := b } default { t := a }` — i.e. `t := min a b`
read off the comparison. -/
@[reducible] private def clampSwitch (a b t : Identifier) : Stmt :=
  .Switch (.PrimCall .Lt [.Var a, .Var b])
    [(0, [.Assign t (.Var b)])]
    [.Assign t (.Var a)]

/-- **Clamp, strictly-below side**: `a < b` takes the default arm, `t := a`. -/
private lemma clamp_lt
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {a b t : Identifier}
    {A B : Literal}
    (ha : (Ok evm σ)[a]!! = A) (hb : (Ok evm σ)[b]!! = B) (hlt : A < B) :
    exec (fuel+1) (clampSwitch a b t) (Ok evm σ) = Ok evm (σ.insert t A) := by
  unfold clampSwitch
  rw [Switch']
  simp only [execSwitchCases, cons, nil, Assign',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMLt',
             List.foldr, insert_Ok]
  rw [ha, hb]
  rw [show fromBool (A < B) = (1 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_true hlt, if_true]]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by decide : ¬ ((0 : UInt256) = (1 : UInt256)))]

/-- **Clamp, at-or-above side**: `¬ (a < b)` takes the 0-arm, `t := b`. -/
private lemma clamp_ge
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {a b t : Identifier}
    {A B : Literal}
    (ha : (Ok evm σ)[a]!! = A) (hb : (Ok evm σ)[b]!! = B) (hge : ¬ (A < B)) :
    exec (fuel+1) (clampSwitch a b t) (Ok evm σ) = Ok evm (σ.insert t B) := by
  unfold clampSwitch
  rw [Switch']
  simp only [execSwitchCases, cons, nil, Assign',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMLt',
             List.foldr, insert_Ok]
  rw [ha, hb]
  rw [show fromBool (A < B) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hge, if_false]]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_pos (rfl : (0 : UInt256) = (0 : UInt256))]

/-- `fun_slice`'s two clamp switches ARE the generic shape. -/
example : clampSwitch "var_end" "_1" "expr"
    = .Switch (.PrimCall .Lt [.Var "var_end", .Var "_1"])
        [(0, [.Assign "expr" (.Var "_1")])]
        [.Assign "expr" (.Var "var_end")] := rfl

/-- **`mcopy` is a model no-op** (the A3-admitted opcode module has an empty
body): the call returns the caller state unchanged.  Any theorem that relies
on the COPIED CONTENT is out of model scope (assumption A3); frame and
control-flow reasoning through `mcopy` calls is exact. -/
lemma mcopy_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {d src l : Literal} :
    execCall (fuel+1) mcopy [] (Ok evm store, [d, src, l]) = Ok evm store := by
  unfold execCall call mcopy
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["dst", "src", "len"], [d, src, l]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["dst", "src", "len"], [d, src, l]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  obtain ⟨e0, σ0, h0⟩ := State_of_isOk hok0
  have he0 : e0 = evm := by
    have h := congrArg State.evm h0
    rw [hevm0] at h
    exact h.symm
  rw [h0]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  rw [he0]
  rfl

end

end generated.L2InteropHandler.L2InteropHandler
