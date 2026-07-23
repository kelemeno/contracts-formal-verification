import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.constant_L2_ATOMIC_FLOW_MANAGER_ADDR
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5196
import specs.KeccakDeterminism

/-
  THE INSERT GATES (L2InteropCommitmentTree dispatcher glue).

  The `insert` entry (source-verbatim (B) boundary, yul 140-262) guards:

  * the APPENDER GATE — `msg.sender` must be the 160-bit-masked
    `L2_ATOMIC_FLOW_MANAGER_ADDR` built-in (`0x10014`), else
    `CommitmentTreeNotAppender`: only the AtomicFlowManager can grow the
    commitment tree;
  * the DEDUP GATE — `valueToIndex[_value] == 0`, else
    `IMTValueAlreadyExists`: the concrete exactly-once enforcement
    (abstract side: `evolution_insert_unique`, #46, and the strictness
    upgrade `window_strict_of_not_mem`).

  The glue is UNSPLIT Yul (calls in expression position), so the condition
  drives go through `Call'`/`evalCall` with call-level closed forms.  This
  file starts the ladder: the constant loader.

  Axiom-free.
-/

namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.dupNamespace false

@[simp] private lemma insert_Ok {evm : EVMState} {store : VarStore}
    {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

private lemma evm_Ok {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

private lemma setEvm_Ok {e E : EVMState} {σ : VarStore} :
    (Ok e σ).setEvm E = Ok E σ := rfl

private lemma lookup_insert_ne_fin_local {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok]; exact lookup_insert_of_ne h

private lemma lookup_insert_self_local {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

private lemma reviveJump_of_isOk_local {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨e₀, σ₀, rfl⟩ := State_of_isOk h; rfl

private lemma evm_setEvm_of_isOk {s : State} {e : EVMState} (h : isOk s) :
    (s🇪⟦e⟧).evm = e := by
  obtain ⟨e₀, σ₀, rfl⟩ := State_of_isOk h; rfl

private lemma evm_insert {s : State} {k : Identifier} {v : Literal} :
    (s⟦k ↦ v⟧).evm = s.evm := by
  cases s <;> rfl

/-- **The appender constant, call level**: `constant_L2_ATOMIC_FLOW_MANAGER_ADDR()`
returns the AFM built-in `65556 = 0x10014` and leaves the caller state
untouched.  Call-level (the pair), so it feeds `evalCall` for the
in-expression occurrence in the appender gate. -/
lemma constant_afm_call {evm : EVMState} {σ : VarStore} {fuel : ℕ} :
    call (fuel+1) [] constant_L2_ATOMIC_FLOW_MANAGER_ADDR (Ok evm σ)
      = (Ok evm σ, [(65556 : Literal)]) := by
  unfold call constant_L2_ATOMIC_FLOW_MANAGER_ADDR
  simp only [params, body, rets, mkOk_initcall_Ok, List.map_nil, List.map_cons]
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  rw [cons, Assign']
  simp only [Lit', insert_Ok]
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  rw [cons, Assign']
  simp only [Lit', insert_Ok]
  rw [cons, nil, Assign']
  simp only [Var', Lit', insert_Ok]
  rfl

/-! ### The appender gate -/

/-- The appender guard of the `insert` entry, source-verbatim (hex
selectors in decimal: `0x742d1b5b = 1949113179`). -/
@[reducible] def appenderIf : Stmt := <s
  if iszero(eq(caller(), and(constant_L2_ATOMIC_FLOW_MANAGER_ADDR(), sub(shl(160, 1), 1))))
  {
      mstore(0, shl(224, 1949113179))
      mstore(4, caller())
      revert(0, 36)
  }
>

/-- **ONLY THE ATOMICFLOWMANAGER APPENDS**: with `msg.sender` the masked AFM
built-in (`65556 &&& (2^160−1) = 65556 = 0x10014`), the guard falls through
with the state untouched. -/
theorem insert_appender_pass
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    (hc : evm.execution_env.source = (65556 : UInt256)) :
    exec (fuel+1) appenderIf (Ok evm σ) = Ok evm σ := by
  unfold appenderIf
  rw [If']
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMEq', EVMAnd', EVMShl', EVMSub', EVMCaller', evm_Ok]
  rw [constant_afm_call]
  try simp only [List.head!]
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMEq', EVMAnd', EVMShl', EVMSub', EVMCaller', evm_Ok]
  simp only [hc]
  try simp only [show Fin.land 65556 (Fin.shiftLeft 1 160 - 1) = (65556 : UInt256) from by decide]
  try simp only [show ((65556 : UInt256) == 65556) = true from by decide]
  try simp only [show decide ((65556 : UInt256) = 65556) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  try simp only [show fromBool (decide True) = (1 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  rw [if_neg (by exact fun h => h rfl)]

/-- **ANYONE ELSE IS REJECTED**: a non-AFM caller reverts with
`CommitmentTreeNotAppender` — the commitment tree grows only through the
AtomicFlowManager. -/
theorem insert_appender_reverts
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    (hc : (evm.execution_env.source : UInt256) ≠ 65556) :
    (exec (fuel+1) appenderIf (Ok evm σ)).evm.reverted = true := by
  unfold appenderIf
  rw [If']
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMEq', EVMAnd', EVMShl', EVMSub', EVMCaller', evm_Ok]
  rw [constant_afm_call]
  try simp only [List.head!]
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMEq', EVMAnd', EVMShl', EVMSub', EVMCaller', evm_Ok]
  try simp only [show Fin.land 65556 (Fin.shiftLeft 1 160 - 1) = (65556 : UInt256) from by decide]
  simp only [hc]
  try simp only [show (decide False) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  try simp only [show fromBool (decide True) = (1 : UInt256) from by decide]
  rw [if_pos (by decide : (1 : UInt256) ≠ 0)]
  -- mstore(0, shl(224, 1949113179))
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMShl', EVMMstore', evm_Ok, setEvm_Ok]
  try simp only [List.head!]
  -- mstore(4, caller())
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMCaller', EVMMstore', evm_Ok, setEvm_Ok]
  try simp only [List.head!]
  -- revert(0, 36)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMRevert', evm_Ok, setEvm_Ok]
  rfl

/-! ### The error encoder, call level -/

/-- **`abi_encode_uint256`, call level**: stores the value at scratch `4`
and returns tail `36` — the `CommitmentTreeNotAppender`/
`IMTValueAlreadyExists` argument encoder, in the pair form the revert-arg
eval consumes. -/
lemma abi_encode_uint256_call {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    {V : Literal} :
    call (fuel+1) [V] abi_encode_uint256 (Ok evm σ)
      = (Ok (evm.mstore 4 V) σ, [(36 : Literal)]) := by
  unfold call abi_encode_uint256
  simp only [params, body, rets, mkOk_initcall_Ok, List.map_nil, List.map_cons]
  have hok0 : isOk ((Ok evm σ)☎️⟦["value0"], [V]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm σ)☎️⟦["value0"], [V]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  set J := (Ok evm σ)☎️⟦["value0"], [V]⟧ with hJ
  obtain ⟨e0, σ0, hJ0⟩ := State_of_isOk hok0
  have he0 : e0 = evm := by
    have h := congrArg State.evm hJ0
    rw [hevm0] at h
    exact h.symm
  have hJ0' : J = Ok evm σ0 := by rw [hJ0, he0]
  rw [hJ0']
  -- tail := 36
  rw [cons, Assign']
  simp only [Lit', insert_Ok]
  -- mstore(4, value0)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMMstore', evm_Ok, setEvm_Ok]
  try simp only [List.head!]
  rw [show (Ok evm (Finmap.insert "tail" 36 σ0))["value0"]!! = V from by
    rw [lookup_insert_ne_fin_local (by decide)]
    rw [← hJ0']
    exact lookup_initcall_1]
  rw [reviveJump_of_isOk_local (by trivial)]
  simp only [overwrite?_of_Ok, setStore_ok]
  rw [lookup_insert_self_local]

/-! ### The valueToIndex accessor, call level -/

private lemma primCall_keccakOut' {s : State} {a b : Literal} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (Clear.KeccakDeterminism.keccakOut s.evm a b).2,
         [(Clear.KeccakDeterminism.keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold Clear.KeccakDeterminism.keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

open Clear.KeccakDeterminism in
/-- **The `valueToIndex` accessor (`mapping_…_5196`), call level**: one
`accOut` step at `(key, 5)`, in the pair form the dedup-gate condition
consumes. -/
lemma mapping_vti_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {key : Literal} :
    call (fuel+1) [key]
        mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5196
        (Ok evm store)
      = (Ok (accOut evm key 5).2 store, [(accOut evm key 5).1]) := by
  unfold call mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5196
  simp only [params, body, rets, mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, nil]
  simp only [ExprStmtPrimCall', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMstore']
  try simp only [multifill', multifill_nil, multifill_cons, overwrite?_of_Ok]
  rw [primCall_keccakOut']
  have hok₀ : isOk ((Ok evm store)☎️⟦["key"], [key]⟧) := isOk_initcall_of_isOk trivial
  have hevm₀ : ((Ok evm store)☎️⟦["key"], [key]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  have hkey : ((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!! = key := lookup_initcall_1
  set host := (((Ok evm store)☎️⟦["key"], [key]⟧)
      🇪⟦((Ok evm store)☎️⟦["key"], [key]⟧).evm.mstore 0
          (((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!!)⟧)
      🇪⟦(((Ok evm store)☎️⟦["key"], [key]⟧)
          🇪⟦((Ok evm store)☎️⟦["key"], [key]⟧).evm.mstore 0
              (((Ok evm store)☎️⟦["key"], [key]⟧)["key"]!!)⟧).evm.mstore 32 5⟧
      with hhost
  have hhost_ok : isOk host := by
    rw [hhost, isOk_setEvm, isOk_setEvm]; exact hok₀
  have hhost_evm : host.evm = (evm.mstore 0 key).mstore 32 5 := by
    rw [hhost, evm_setEvm_of_isOk (by rw [isOk_setEvm]; exact hok₀),
        evm_setEvm_of_isOk hok₀, hevm₀, hkey]
  rw [hhost_evm]
  unfold accOut
  generalize hout : keccakOut ((evm.mstore 0 key).mstore 32 5) 0 64 = out
  try simp only [multifill_cons, multifill_nil]
  have hsetEvm_ok : isOk (host.setEvm out.2) := by
    rw [isOk_setEvm]; exact hhost_ok
  have hin_ok : isOk ((host.setEvm out.2)⟦"dataSlot" ↦ out.1⟧) := by
    rw [isOk_insert]; exact hsetEvm_ok
  rw [lookup_insert' hsetEvm_ok]
  rw [reviveJump_of_isOk_local hin_ok]
  obtain ⟨ei, si, hi⟩ := State_of_isOk hin_ok
  have hi_evm : ei = out.2 := by
    have h := congrArg State.evm hi
    rw [evm_insert, evm_setEvm_of_isOk hhost_ok] at h
    exact h.symm
  rw [hi]
  simp only [overwrite?_of_Ok, setStore_ok]
  rw [hi_evm]

/-! ### The dedup gate -/

private lemma lookup_ok_evm_local {σ : VarStore} {k : Identifier}
    (e e' : EVMState) : (Ok e σ)[k]!! = (Ok e' σ)[k]!! := rfl

/-- The dedup guard, source-verbatim (`0x3402883b = 872581179`):
`valueToIndex[_value]` must be zero. -/
@[reducible] def dedupIf : Stmt := <s
  if iszero(iszero(sload(mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5196(value0))))
  {
      mstore(0, shl(225, 872581179))
      revert(0, abi_encode_uint256(value0))
  }
>

open Clear.KeccakDeterminism in
/-- **A FRESH VALUE PASSES**: with `valueToIndex[V]` empty the guard falls
through; the state carries the accessor's keccak step (the condition
threads `accOut`). -/
theorem insert_dedup_pass
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {V : Literal}
    (hv : (Ok evm σ)["value0"]!! = V)
    (hz : (accOut evm V 5).2.sload ((accOut evm V 5).1) = 0) :
    exec (fuel+1) dedupIf (Ok evm σ) = Ok (accOut evm V 5).2 σ := by
  unfold dedupIf
  rw [If']
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMSload', evm_Ok]
  rw [hv, mapping_vti_call]
  try simp only [List.head!]
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMSload', evm_Ok]
  simp only [hz]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  try simp only [show fromBool (decide True) = (1 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  rw [if_neg (by exact fun h => h rfl)]

open Clear.KeccakDeterminism in
/-- **A DUPLICATE VALUE IS REJECTED** — the concrete exactly-once
enforcement: with `valueToIndex[V]` non-empty the insert reverts with
`IMTValueAlreadyExists`.  (Abstract mirror: `evolution_insert_unique`,
#46; strictness upgrade: `window_strict_of_not_mem`.) -/
theorem insert_dedup_reverts
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {V : Literal}
    (hv : (Ok evm σ)["value0"]!! = V)
    (hnz : (accOut evm V 5).2.sload ((accOut evm V 5).1) ≠ 0) :
    (exec (fuel+1) dedupIf (Ok evm σ)).evm.reverted = true := by
  unfold dedupIf
  rw [If']
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMSload', evm_Ok]
  rw [hv, mapping_vti_call]
  try simp only [List.head!]
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMSload', evm_Ok]
  simp only [show (decide ((accOut evm V 5).2.sload ((accOut evm V 5).1) = 0)) = false
    from decide_eq_false hnz]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  try simp only [show fromBool (decide True) = (1 : UInt256) from by decide]
  rw [if_pos (by decide : (1 : UInt256) ≠ 0)]
  -- mstore(0, shl(225, 872581179))
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMShl', EVMMstore', evm_Ok, setEvm_Ok]
  try simp only [List.head!]
  -- revert(0, abi_encode_uint256(value0))
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMRevert', evm_Ok, setEvm_Ok]
  rw [lookup_ok_evm_local _ evm, hv, abi_encode_uint256_call]
  try simp only [List.head!]
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMRevert', evm_Ok, setEvm_Ok]
  rfl

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
