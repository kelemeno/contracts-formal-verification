import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import generated.L2InteropHandler.L2InteropHandler.checked_sub_uint256
import generated.L2InteropHandler.L2InteropHandler.array_allocation_size_bytes

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

end

end generated.L2InteropHandler.L2InteropHandler
