import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.constant_L2_ATOMIC_FLOW_MANAGER_ADDR
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5196
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199
import specs.KeccakDeterminism
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_hashLeaf
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.allocate_memory_5179
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_hash_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_leaf_storage_user

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
     L2InteropCommitmentTree.Common

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.dupNamespace false

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

/-! ### `fun_hashLeaf`, call level -/

open Clear.KeccakDeterminism in
/-- **`fun_hashLeaf`, call level** — the leaf-struct hash in pair form for
its expression-position occurrences in the insert glue
(`updateLeaf(…, hashLeaf(e))`, `pushNewLeaf(hashLeaf(e))`).  Transplant of
`hashLeaf_call_acc`. -/
lemma hashLeaf_vcall
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {leaf : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615) :
    call (fuel+1) [leaf] fun_hashLeaf (Ok evm σ)
      = (Ok (hashLeafOut evm leaf).2 σ, [(hashLeafOut evm leaf).1]) := by
  have hbody : fun_hashLeaf.body
      = [block_1948431615937796266, block_2512525436326504558,
         block_5488197900316908801, block_7615139809432579602] := by
    rfl
  have hparams : fun_hashLeaf.params = ["var_leaf_mpos"] := rfl
  have hrets : fun_hashLeaf.rets = ["var"] := rfl
  unfold call
  simp only [hparams, hrets, hbody]
  simp only [multifill', mkOk_initcall_Ok, List.map_nil, List.map_cons]
  rw [cons, cons, cons, cons, nil]
  have hok0 : isOk ((Ok evm σ)☎️⟦["var_leaf_mpos"], [leaf]⟧) := isOk_initcall_of_isOk trivial
  obtain ⟨e0, σ0, h0⟩ := State_of_isOk hok0
  have hleaf0 : ((Ok evm σ)☎️⟦["var_leaf_mpos"], [leaf]⟧)["var_leaf_mpos"]!! = leaf :=
    lookup_initcall_1
  have he0 : e0 = evm := by
    have h := congrArg State.evm h0
    rw [show ((Ok evm σ)☎️⟦["var_leaf_mpos"], [leaf]⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at h
    exact h.symm
  rw [h0, he0] at hleaf0
  simp only [h0, he0]
  simp only [hashLeaf_chunk1 hleaf0]
  have h1 : (Ok evm (((((σ0.insert "_1" (evm.mload leaf)).insert
      "split_expr_0" (leaf + 32)).insert "_2" (evm.mload (leaf + 32))).insert
      "split_expr_1" (leaf + 64)).insert "_3" (evm.mload (leaf + 64))))["_1"]!!
      = evm.mload leaf := by
    rw [lookup_insert_ne_fin_local (by decide), lookup_insert_ne_fin_local (by decide),
        lookup_insert_ne_fin_local (by decide), lookup_insert_ne_fin_local (by decide)]
    exact lookup_insert_self_local
  have h2 : (Ok evm (((((σ0.insert "_1" (evm.mload leaf)).insert
      "split_expr_0" (leaf + 32)).insert "_2" (evm.mload (leaf + 32))).insert
      "split_expr_1" (leaf + 64)).insert "_3" (evm.mload (leaf + 64))))["_2"]!!
      = evm.mload (leaf + 32) := by
    rw [lookup_insert_ne_fin_local (by decide), lookup_insert_ne_fin_local (by decide)]
    exact lookup_insert_self_local
  simp only [hashLeaf_chunk2 h1 h2]
  set σ2 := ((((((σ0.insert "_1" (evm.mload leaf)).insert
      "split_expr_0" (leaf + 32)).insert "_2" (evm.mload (leaf + 32))).insert
      "split_expr_1" (leaf + 64)).insert "_3" (evm.mload (leaf + 64))).insert
      "expr_mpos" (evm.mload 64)).insert "_4" (evm.mload 64 + 32) with hσ2
  set E2 := (evm.mstore (evm.mload 64 + 32) (evm.mload leaf)).mstore (evm.mload 64 + 64)
      (evm.mload (leaf + 32)) with hE2
  have hP : (Ok E2 (σ2.insert "split_expr_2" (evm.mload 64 + 64)))["expr_mpos"]!!
      = evm.mload 64 := by
    rw [lookup_insert_ne_fin_local (by decide), hσ2,
        lookup_insert_ne_fin_local (by decide)]
    exact lookup_insert_self_local
  have h3 : (Ok E2 (σ2.insert "split_expr_2" (evm.mload 64 + 64)))["_3"]!!
      = evm.mload (leaf + 64) := by
    rw [lookup_insert_ne_fin_local (by decide), hσ2,
        lookup_insert_ne_fin_local (by decide), lookup_insert_ne_fin_local (by decide)]
    exact lookup_insert_self_local
  simp only [hashLeaf_chunk3 hP h3 hp]
  set E5 := ((E2.mstore (evm.mload 64 + 96) (evm.mload (leaf + 64))).mstore
      (evm.mload 64) 96).mstore 64 (evm.mload 64 + 128) with hE5
  set σ3 := ((σ2.insert "split_expr_2" (evm.mload 64 + 64)).insert
      "split_expr_3" (evm.mload 64 + 96)).insert "split_expr_4" (E5.mload (evm.mload 64)) with hσ3
  have hx : (Ok E5 σ3)["_4"]!! = evm.mload 64 + 32 := by
    rw [hσ3, lookup_insert_ne_fin_local (by decide), lookup_insert_ne_fin_local (by decide),
        lookup_insert_ne_fin_local (by decide), hσ2]
    exact lookup_insert_self_local
  have hl : (Ok E5 σ3)["split_expr_4"]!! = E5.mload (evm.mload 64) := by
    rw [hσ3]
    exact lookup_insert_self_local
  simp only [hashLeaf_chunk4 hx hl]
  have hokF : isOk (Ok (keccakOut E5 (evm.mload 64 + 32) (E5.mload (evm.mload 64))).2
      (σ3.insert "var" (keccakOut E5 (evm.mload 64 + 32) (E5.mload (evm.mload 64))).1)) := trivial
  have hvar : (Ok (keccakOut E5 (evm.mload 64 + 32) (E5.mload (evm.mload 64))).2
      (σ3.insert "var" (keccakOut E5 (evm.mload 64 + 32) (E5.mload (evm.mload 64))).1))["var"]!!
      = (keccakOut E5 (evm.mload 64 + 32) (E5.mload (evm.mload 64))).1 :=
    lookup_insert_self_local
  simp only [hvar]
  rw [reviveJump_of_isOk_local hokF]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  have halign : keccakOut E5 (evm.mload 64 + 32) (E5.mload (evm.mload 64))
      = hashLeafOut evm leaf := by
    rw [hE5, hE2]
    unfold hashLeafOut leafScratchEvm
    rfl
  rw [halign]

/-! ### The struct allocator (`allocate_memory_5179`) -/

private lemma val_add_96_local {p : UInt256} (hp : p.val + 96 ≤ 18446744073709551615) :
    ((p + (96 : UInt256))).val = p.val + 96 := by
  have h96 : ((96 : UInt256)).val = 96 := by decide
  have hlt : p.val + ((96 : UInt256)).val < UInt256.size := by
    have hs : UInt256.size = 2 ^ 256 := by norm_num
    omega
  calc ((p + (96 : UInt256))).val
      = (p.val + ((96 : UInt256)).val) % UInt256.size := rfl
    _ = p.val + ((96 : UInt256)).val := Nat.mod_eq_of_lt hlt
    _ = p.val + 96 := by rw [h96]

/-- Base `finalize_allocation` at size 96 (clone of the 128 variant). -/
lemma finalize_allocation_96_base_call
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
  -- the two guards evaluate to 0 given `hp`
  have hMAXv : ((18446744073709551615 : UInt256)).val = 18446744073709551615 := by decide
  have hgt : fromBool (p + 96 > (18446744073709551615 : UInt256)) = (0 : UInt256) := by
    rw [decide_eq_false (by
      intro h
      rw [gt_iff_lt, Fin.lt_def, hMAXv, val_add_96_local hp] at h
      omega)]
    rfl
  have hlt : fromBool (p + 96 < p) = (0 : UInt256) := by
    rw [decide_eq_false (by
      intro h
      rw [Fin.lt_def, val_add_96_local hp] at h
      omega)]
    rfl
  -- resolve the newFreePtr binding, then the two guard values
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
  -- the guard `or` is 0: skip the panic branch
  have l4a : (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)["split_expr_3"]!!
      = 0 := by
    rw [lookup_insert_of_ne (by decide)]; exact lookup_insert' hok3
  have l4b : (B⟦"split_expr_0" ↦ 127⟧⟦"split_expr_1" ↦ m31⟧⟦"split_expr_2" ↦ (96 : UInt256)⟧⟦"newFreePtr" ↦ p + 96⟧⟦"split_expr_3" ↦ (0 : UInt256)⟧⟦"split_expr_4" ↦ (0 : UInt256)⟧)["split_expr_4"]!!
      = 0 := lookup_insert' hok4
  rw [l4a, l4b]
  rw [show Fin.lor (0 : UInt256) 0 = (0 : UInt256) from by decide]
  simp only [head', List.head!]
  rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
  -- trailing mstore(64, newFreePtr) on the else-branch state
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

/-! ## `fun_hashLeaf` closed form — the IMT leaf hash

`hashLeaf(leaf_mpos)` loads the three leaf fields `(value, nextIndex,
nextValue)` from the struct at `leaf_mpos`, abi-encodes them at the free
pointer `P = mload(64)` (fields at `P+32/P+64/P+96`, length word `96` at `P`),
finalizes the allocation (bumping the free pointer to `P+96`), and hashes the
96-byte field region: `keccak256(P+32, mload(P))`.  `leafScratchEvm` is the
evm after the five writes; the returned hash is `keccakOut` at `(P+32,
mload(P))` — the length is left as the symbolic read-back (proving
`mload(P) = 96` is the separate round-trip lemma, next). -/


/-- **The 96-byte struct allocator**: returns the free pointer and bumps it
by 96 — the `IMTLeaf memory` allocation the insert glue performs twice. -/
lemma allocate_memory_5179_call
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {v : Identifier}
    (hp : (evm.mload 64).val + 96 ≤ 18446744073709551615) :
    execCall (fuel+1) allocate_memory_5179 [v] (Ok evm σ, [])
      = Ok (evm.mstore 64 (evm.mload 64 + 96))
          (Finmap.insert v (evm.mload 64) σ) := by
  unfold execCall call allocate_memory_5179
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  set s0 := (Ok evm σ)☎️⟦[], []⟧ with hs0
  have hok0 : isOk s0 := isOk_initcall_of_isOk trivial
  have hevm0 : s0.evm = evm := by
    rw [hs0]; unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  obtain ⟨e0, σ0, hs0eq⟩ := State_of_isOk hok0
  have he0' : e0 = evm := by
    have h := congrArg State.evm hs0eq
    rw [hevm0] at h; exact h.symm
  subst e0
  rw [hs0eq]
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
  rw [lookup_insert_self_local]
  rw [finalize_allocation_96_base_call hp]
  simp only [setEvm_Ok]
  rw [lookup_insert_self_local]
  rw [reviveJump_of_isOk_local (by trivial)]
  try simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  try simp only [multifill_cons, multifill_nil, insert_Ok]

/-! ### The leaves accessor, call level -/

open Clear.KeccakDeterminism in
/-- **The `leaves` accessor (`mapping_…_5199`), call level**: one `accOut`
step at `(key, 4)`, for its expression-position uses in the insert glue
(`copy_struct_to_storage(mapping_5199(idx), ptr)`). -/
lemma mapping_leaves4_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {key : Literal} :
    call (fuel+1) [key]
        mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199
        (Ok evm store)
      = (Ok (accOut evm key 4).2 store, [(accOut evm key 4).1]) := by
  unfold call mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199
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

/-! ### The retarget-staging chunk of the insert glue -/

/-- The retarget staging, source-verbatim (yul 243-250): read the low
leaf's three fields, allocate the updated struct
`⟨lowLeaf.value, newIndex, _value⟩` in memory, and copy it to storage at
`leaves[lowLeafIndex]`. -/
@[reducible] def retargetChunk : Stmt := <s
  {
      let _4 := mload(add(var_lowLeaf_mpos, 32))
      let _5 := mload(add(var_lowLeaf_mpos, 64))
      let _6 := mload(var_lowLeaf_mpos)
      let expr_mpos := allocate_memory_5179()
      mstore(expr_mpos, _6)
      mstore(add(expr_mpos, 32), _1)
      mstore(add(expr_mpos, 64), value0)
      copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf(mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199(var_lowLeafIndex), expr_mpos)
  }
>

open Clear.KeccakDeterminism in
/-- The evm after the retarget staging: allocator bump, three struct-field
scratch writes at the fresh pointer `P = mload 64`, the leaves-slot keccak
step on that state, and the three-field storage copy at
`keccak(lowIdx ‖ 4)`. -/
@[reducible] def retargetStageEvm (evm : EVMState) (LM NI V IX : UInt256) : EVMState :=
  let P := evm.mload 64
  let E4 := (((evm.mstore 64 (evm.mload 64 + 96)).mstore P (evm.mload LM)).mstore
      (P + 32) NI).mstore (P + 64) V
  let EK := (accOut E4 IX 4).2
  let SL := (accOut E4 IX 4).1
  ((EK.sstore SL (EK.mload P)).sstore
      (SL + 1) (EK.mload (P + 32))).sstore
      (SL + 2) (EK.mload (P + 64))

open Clear.KeccakDeterminism in
/-- **Retarget-staging closed form.** -/
lemma retargetStage_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {LM NI V IX : Literal}
    (hlm : (Ok evm σ)["var_lowLeaf_mpos"]!! = LM)
    (h1 : (Ok evm σ)["_1"]!! = NI)
    (hv : (Ok evm σ)["value0"]!! = V)
    (hix : (Ok evm σ)["var_lowLeafIndex"]!! = IX)
    (hp : (evm.mload 64).val + 96 ≤ 18446744073709551615) :
    exec (fuel+1) retargetChunk (Ok evm σ)
      = Ok (retargetStageEvm evm LM NI V IX)
          ((((σ.insert "_4" (evm.mload (LM + 32))).insert
            "_5" (evm.mload (LM + 64))).insert
            "_6" (evm.mload LM)).insert
            "expr_mpos" (evm.mload 64)) := by
  unfold retargetChunk
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload', EVMAdd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [hlm]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload', EVMAdd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_ne_fin_local (by decide), hlm]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_ne_fin_local (by decide), lookup_insert_ne_fin_local (by decide), hlm]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [allocate_memory_5179_call hp]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_local]
  rw [lookup_insert_ne_fin_local (by decide), lookup_ok_evm_local _ evm,
      lookup_insert_self_local]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMstore', EVMAdd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_local]
  rw [lookup_insert_ne_fin_local (by decide), lookup_insert_ne_fin_local (by decide),
      lookup_insert_ne_fin_local (by decide), lookup_insert_ne_fin_local (by decide),
      lookup_ok_evm_local _ evm, h1]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMstore', EVMAdd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_local]
  rw [lookup_insert_ne_fin_local (by decide), lookup_insert_ne_fin_local (by decide),
      lookup_insert_ne_fin_local (by decide), lookup_insert_ne_fin_local (by decide),
      lookup_ok_evm_local _ evm, hv]
  rw [cons, nil, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_local]
  rw [lookup_insert_ne_fin_local (by decide), lookup_insert_ne_fin_local (by decide),
      lookup_insert_ne_fin_local (by decide), lookup_insert_ne_fin_local (by decide),
      lookup_ok_evm_local _ evm, hix]
  rw [mapping_leaves4_call]
  try simp only [List.head!]
  try simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [copy_leaf_call]
  simp only [setEvm_Ok]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
