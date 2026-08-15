import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.constant_L2_ATOMIC_FLOW_MANAGER_ADDR
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_uint256_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5196
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199
import specs.KeccakDeterminism
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_hashLeaf
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.allocate_memory_5179
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.read_from_storage_reference_type_struct_IMTLeaf
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.increment_uint256
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_hash_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_leaf_storage_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_update_5205_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_pad_user
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_pushNewLeaf
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_updateLeaf_5205

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

/-! ### The new-leaf + valueToIndex chunk of the insert glue -/

/-- The new-leaf staging, source-verbatim (yul 252-259): allocate
`⟨_value, oldNextIndex, oldNextValue⟩`, copy it to `leaves[newIndex]`, and
register `valueToIndex[_value] := newIndex`. -/
@[reducible] def newLeafChunk : Stmt := <s
  {
      let expr_mpos_1 := allocate_memory_5179()
      mstore(expr_mpos_1, value0)
      mstore(add(expr_mpos_1, 32), _4)
      mstore(add(expr_mpos_1, 64), _5)
      copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf(mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199(_1), expr_mpos_1)
      sstore(mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5196(value0), _1)
  }
>

open Clear.KeccakDeterminism in
/-- The evm after the new-leaf staging: allocator bump, three scratch
writes, the `leaves[newIndex]` keccak step + three-field copy, then the
`valueToIndex[_value]` keccak step + registration write. -/
@[reducible] def newLeafStageEvm (evm : EVMState) (V NI4 NV5 IX1 : UInt256) : EVMState :=
  let P := evm.mload 64
  let E4 := (((evm.mstore 64 (evm.mload 64 + 96)).mstore P V).mstore
      (P + 32) NI4).mstore (P + 64) NV5
  let EK := (accOut E4 IX1 4).2
  let SL := (accOut E4 IX1 4).1
  let E5 := ((EK.sstore SL (EK.mload P)).sstore
      (SL + 1) (EK.mload (P + 32))).sstore
      (SL + 2) (EK.mload (P + 64))
  (accOut E5 V 5).2.sstore (accOut E5 V 5).1 IX1

open Clear.KeccakDeterminism in
/-- **New-leaf-staging closed form.** -/
lemma newLeafStage_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {V NI4 NV5 IX1 : Literal}
    (hv : (Ok evm σ)["value0"]!! = V)
    (h4 : (Ok evm σ)["_4"]!! = NI4)
    (h5 : (Ok evm σ)["_5"]!! = NV5)
    (h1 : (Ok evm σ)["_1"]!! = IX1)
    (hp : (evm.mload 64).val + 96 ≤ 18446744073709551615) :
    exec (fuel+1) newLeafChunk (Ok evm σ)
      = Ok (newLeafStageEvm evm V NI4 NV5 IX1)
          (σ.insert "expr_mpos_1" (evm.mload 64)) := by
  unfold newLeafChunk
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
  rw [lookup_insert_ne_fin_local (by decide), lookup_ok_evm_local _ evm, hv]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMstore', EVMAdd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_local]
  rw [lookup_insert_ne_fin_local (by decide),
      lookup_ok_evm_local _ evm, h4]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMstore', EVMAdd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_local]
  rw [lookup_insert_ne_fin_local (by decide),
      lookup_ok_evm_local _ evm, h5]
  rw [cons, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_local]
  rw [lookup_insert_ne_fin_local (by decide),
      lookup_ok_evm_local _ evm, h1]
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
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMSstore',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_ne_fin_local (by decide),
      lookup_ok_evm_local _ evm, hv]
  rw [mapping_vti_call]
  try simp only [List.head!]
  try simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMSstore',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_ne_fin_local (by decide),
      lookup_ok_evm_local _ evm, h1]

/-! ### The low-leaf read chunk of the insert glue -/

/-- The initial low-leaf read, source-verbatim (yul 194-198): pin the
candidate index, materialize `self.leaves[lowLeafIndex]` in memory, read
its `value` field. -/
@[reducible] def lowLeafReadChunk : Stmt := <s
  {
      let var_lowLeafIndex := value1
      let var_lowLeaf_mpos := read_from_storage_reference_type_struct_IMTLeaf(mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199(value1))
      let _2 := mload(var_lowLeaf_mpos)
  }
>

open Clear.KeccakDeterminism in
/-- **Low-leaf read closed form**: the leaves-slot keccak step, the struct
materialization (`leafReadEvm`), and the `value`-field readback. -/
lemma lowLeafRead_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {IX : Literal}
    (hix : (Ok evm σ)["value1"]!! = IX)
    (hp : ((accOut evm IX 4).2.mload 64).val + 96 ≤ 18446744073709551615) :
    exec (fuel+1) lowLeafReadChunk (Ok evm σ)
      = Ok (leafReadEvm (accOut evm IX 4).2 (accOut evm IX 4).1)
          (((σ.insert "var_lowLeafIndex" IX).insert
            "var_lowLeaf_mpos" ((accOut evm IX 4).2.mload 64)).insert
            "_2" ((leafReadEvm (accOut evm IX 4).2 (accOut evm IX 4).1).mload
              ((accOut evm IX 4).2.mload 64))) := by
  unfold lowLeafReadChunk
  rw [cons, LetEq']
  simp only [Var', insert_Ok]
  rw [hix]
  rw [cons, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_ne_fin_local (by decide), hix]
  rw [mapping_leaves4_call]
  try simp only [List.head!]
  try simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [read_leaf_call hp]
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_insert_self_local]

/-! ### The two-word error encoder and the value-order gate -/

/-- **`abi_encode_uint256_uint256`, call level**: two scratch writes,
tail `68`. -/
lemma abi_encode_uint256_uint256_call
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {V1 V2 : Literal} :
    call (fuel+1) [V1, V2] abi_encode_uint256_uint256 (Ok evm σ)
      = (Ok ((evm.mstore 4 V1).mstore 36 V2) σ, [(68 : Literal)]) := by
  unfold call abi_encode_uint256_uint256
  simp only [params, body, rets, mkOk_initcall_Ok, List.map_nil, List.map_cons]
  have hok0 : isOk ((Ok evm σ)☎️⟦["value0", "value1"], [V1, V2]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm σ)☎️⟦["value0", "value1"], [V1, V2]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  set J := (Ok evm σ)☎️⟦["value0", "value1"], [V1, V2]⟧ with hJ
  obtain ⟨e0, σ0, hJ0⟩ := State_of_isOk hok0
  have he0 : e0 = evm := by
    have h := congrArg State.evm hJ0
    rw [hevm0] at h
    exact h.symm
  have hJ0' : J = Ok evm σ0 := by rw [hJ0, he0]
  rw [hJ0']
  rw [cons, Assign']
  simp only [Lit', insert_Ok]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMMstore', evm_Ok, setEvm_Ok]
  try simp only [List.head!]
  rw [show (Ok evm (Finmap.insert "tail" 68 σ0))["value0"]!! = V1 from by
    rw [lookup_insert_ne_fin_local (by decide)]
    rw [← hJ0']
    exact lookup_initcall_1]
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMMstore', evm_Ok, setEvm_Ok]
  try simp only [List.head!]
  rw [show (Ok ((evm.mstore 4 V1)) (Finmap.insert "tail" 68 σ0))["value1"]!! = V2 from by
    rw [lookup_insert_ne_fin_local (by decide)]
    rw [lookup_ok_evm_local _ evm]
    rw [← hJ0']
    exact lookup_initcall_2 (by decide)]
  rw [reviveJump_of_isOk_local (by trivial)]
  simp only [overwrite?_of_Ok, setStore_ok]
  rw [lookup_insert_self_local]

/-- The value-order guard, source-verbatim (`0x74470b8f = 1950813071`):
the window's low value must be strictly below the inserted value. -/
@[reducible] def valueOrderIf : Stmt := <s
  if iszero(lt(_2, value0))
  {
      mstore(0, shl(224, 1950813071))
      revert(0, abi_encode_uint256_uint256(_2, value0))
  }
>

/-- **A PROPER LOW LEAF PASSES**: `lowLeaf.value < _value` falls through
untouched. -/
theorem valueOrder_pass
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {L V : Literal}
    (h2 : (Ok evm σ)["_2"]!! = L)
    (hv : (Ok evm σ)["value0"]!! = V)
    (hlt : L < V) :
    exec (fuel+1) valueOrderIf (Ok evm σ) = Ok evm σ := by
  unfold valueOrderIf
  rw [If']
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMLt', evm_Ok]
  rw [h2, hv]
  try simp only [List.head!]
  simp only [show decide (L < V) = true from decide_eq_true hlt]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  try simp only [show fromBool (decide True) = (1 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  rw [if_neg (by exact fun h => h rfl)]

/-- **A MISORDERED LOW LEAF IS REJECTED**: `lowLeaf.value ≥ _value` reverts
`IMTLowLeafValueTooLarge` — the concrete window-order guard (`W₀.key < v`
of the abstract `Evolution` step). -/
theorem valueOrder_reverts
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {L V : Literal}
    (h2 : (Ok evm σ)["_2"]!! = L)
    (hv : (Ok evm σ)["value0"]!! = V)
    (hge : ¬ (L < V)) :
    (exec (fuel+1) valueOrderIf (Ok evm σ)).evm.reverted = true := by
  unfold valueOrderIf
  rw [If']
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMLt', evm_Ok]
  rw [h2, hv]
  try simp only [List.head!]
  simp only [show decide (L < V) = false from decide_eq_false hge]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  try simp only [show fromBool (decide True) = (1 : UInt256) from by decide]
  rw [if_pos (by decide : (1 : UInt256) ≠ 0)]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMShl', EVMMstore', evm_Ok, setEvm_Ok]
  try simp only [List.head!]
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMRevert', evm_Ok, setEvm_Ok]
  rw [lookup_ok_evm_local _ evm, h2]
  rw [lookup_ok_evm_local _ evm, hv]
  rw [abi_encode_uint256_uint256_call]
  try simp only [List.head!]
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMRevert', evm_Ok, setEvm_Ok]
  rfl

/-! ### The low-leaf search loop, zero iterations

The insert glue walks `lowLeaf.nextValue` links (yul 208-240) until the
window closes: `nextValue = 0` (end of the linked list) or
`nextValue ≥ _value`.  The ZERO-ITERATION closed form: the first body pass
hits the `break`, the post (`++attempts`) never runs, the evm is untouched
— only the loop scratch (`_3`, `expr`) is written. -/

private lemma exec_checkpoint_local {c : Jump} {fuel : ℕ} {stmt : Stmt} :
    exec fuel stmt (Checkpoint c) = Checkpoint c := by
  have h := Clear.JumpLemmas.exec_Jump (c := c) (s := Checkpoint c)
    (fuel := fuel) (stmt := stmt) rfl
  rcases hres : exec fuel stmt (Checkpoint c) with _ | _ | c'
  · rw [hres] at h; exact absurd h (by unfold isJump; simp)
  · rw [hres] at h; exact absurd h (by unfold isJump; simp)
  · rw [hres] at h
    have : c = c' := h
    rw [this]

private lemma break_block_local {fuel : ℕ} {evm : EVMState} {σ : VarStore} :
    exec (fuel+1) (.Block [Stmt.Break]) (Ok evm σ) = Checkpoint (.Break evm σ) := by
  rw [cons, nil, Break']
  rfl

/-- The `lt(_3, value0)` retest block of the search loop (the second `&&`
conjunct), as its own closed form to keep the `cons` drives unambiguous. -/
private lemma ltAssign_block {fuel : ℕ} {evm : EVMState} {σ : VarStore} {A B : Literal}
    (h3 : (Ok evm σ)["_3"]!! = A)
    (hv : (Ok evm σ)["value0"]!! = B) :
    exec (fuel+1) (.Block [AssignPrimCall ["expr"] .Lt [Var "_3", Var "value0"]])
        (Ok evm σ)
      = Ok evm (Finmap.insert "expr" (fromBool (A < B)) σ) := by
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMLt', insert_Ok]
  rw [h3, hv]

/-- The low-leaf search loop, source-verbatim (yul 208-240; hex selector in
decimal: `0x6c3f0733 = 1816069939` — `IMTLowLeafNextTooSmall`). -/
@[reducible] def searchLoopFor : Stmt := <s
  for { }
  1
  {
      var_attempts := increment_uint256(var_attempts)
  }
  {
      let _3 := mload(add(var_lowLeaf_mpos, 64))
      let expr := iszero(iszero(_3))
      if expr
      {
          expr := lt(_3, value0)
      }
      if iszero(expr) { break }
      if eq(var_attempts, 5)
      {
          mstore(0, shl(225, 1816069939))
          revert(0, abi_encode_uint256_uint256(_3, value0))
      }
      var_lowLeafIndex := mload(add(var_lowLeaf_mpos, 32))
      var_lowLeaf_mpos := read_from_storage_reference_type_struct_IMTLeaf(mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199(var_lowLeafIndex))
  }
>

/-- **The first search pass breaks** when the window already closes:
`nextValue = 0` or `¬ (nextValue < _value)`.  Body-until-break closed form:
the evm is untouched, the store gains `"_3" ↦ NV` then `"expr" ↦ 0` (in the
retest case the transient `"expr" ↦ 1` is overwritten, collapsed by
`Finmap.insert_insert`). -/
lemma searchBody_break
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {LM V NV : Literal}
    (hlm : (Ok evm σ)["var_lowLeaf_mpos"]!! = LM)
    (hv : (Ok evm σ)["value0"]!! = V)
    (hnv : evm.mload (LM + 64) = NV)
    (hwin : NV = 0 ∨ ¬ (NV < V)) :
    exec (fuel+1) (.Block <ss
      {
          let _3 := mload(add(var_lowLeaf_mpos, 64))
          let expr := iszero(iszero(_3))
          if expr
          {
              expr := lt(_3, value0)
          }
          if iszero(expr) { break }
          if eq(var_attempts, 5)
          {
              mstore(0, shl(225, 1816069939))
              revert(0, abi_encode_uint256_uint256(_3, value0))
          }
          var_lowLeafIndex := mload(add(var_lowLeaf_mpos, 32))
          var_lowLeaf_mpos := read_from_storage_reference_type_struct_IMTLeaf(mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199(var_lowLeafIndex))
      }
    >) (Ok evm σ)
      = Checkpoint (.Break evm
          (Finmap.insert "expr" 0 (Finmap.insert "_3" NV σ))) := by
  -- let _3 := mload(add(var_lowLeaf_mpos, 64))
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMMload', EVMAdd',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [hlm]
  try simp only [head', List.head!]
  rw [hnv]
  -- let expr := iszero(iszero(_3))
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMIszero', insert_Ok]
  try simp only [head', List.head!]
  rw [lookup_insert_self_local]
  by_cases hz : NV = 0
  · -- nextValue = 0: expr = 0, the retest if is skipped, iszero(expr) breaks
    rw [show fromBool (NV = 0) = (1 : UInt256) from by
      rw [decide_eq_true hz]; rfl]
    rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
    -- if expr { … } — skipped
    rw [cons, If']
    simp only [evalArgs, evalTail, cons', head', reverse', Lit', Var',
               List.reverse_cons, List.reverse_nil, List.nil_append,
               List.singleton_append]
    rw [lookup_insert_self_local]
    try simp only [head', List.head!]
    rw [if_neg (by decide : ¬ ((0 : UInt256) ≠ 0))]
    -- if iszero(expr) { break } — taken
    rw [cons, If']
    simp only [evalArgs, evalTail, cons', head', reverse', multifill',
               PrimCall', Lit', Var', execPrimCall, evalPrimCall,
               List.reverse_cons, List.reverse_nil, List.nil_append,
               List.singleton_append, EVMIszero']
    rw [lookup_insert_self_local]
    rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
    try simp only [head', List.head!]
    rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
    rw [break_block_local]
    rw [cons, exec_checkpoint_local, cons, exec_checkpoint_local,
        cons, nil, exec_checkpoint_local]
  · -- nextValue ≠ 0: expr = 1, the retest runs, lt fails, iszero(expr) breaks
    have hge : ¬ (NV < V) := by
      rcases hwin with h | h
      · exact absurd h hz
      · exact h
    rw [show fromBool (NV = 0) = (0 : UInt256) from by
      rw [decide_eq_false hz]; rfl]
    rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
    -- if expr { … } — taken
    rw [cons, If']
    simp only [evalArgs, evalTail, cons', head', reverse', Lit', Var',
               List.reverse_cons, List.reverse_nil, List.nil_append,
               List.singleton_append]
    rw [lookup_insert_self_local]
    try simp only [head', List.head!]
    rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
    -- expr := lt(_3, value0) — the retest fails
    have h3 : (Ok evm (Finmap.insert "expr" 1
        (Finmap.insert "_3" NV σ)))["_3"]!! = NV := by
      rw [lookup_insert_ne_fin_local (by decide), lookup_insert_self_local]
    have hv2 : (Ok evm (Finmap.insert "expr" 1
        (Finmap.insert "_3" NV σ)))["value0"]!! = V := by
      rw [lookup_insert_ne_fin_local (by decide),
          lookup_insert_ne_fin_local (by decide)]
      exact hv
    rw [ltAssign_block h3 hv2]
    rw [show fromBool (NV < V) = (0 : UInt256) from by
      rw [decide_eq_false hge]; rfl]
    rw [Finmap.insert_insert]
    -- if iszero(expr) { break } — taken
    rw [cons, If']
    simp only [evalArgs, evalTail, cons', head', reverse', multifill',
               PrimCall', Lit', Var', execPrimCall, evalPrimCall,
               List.reverse_cons, List.reverse_nil, List.nil_append,
               List.singleton_append, EVMIszero']
    rw [lookup_insert_self_local]
    rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
    try simp only [head', List.head!]
    rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
    rw [break_block_local]
    rw [cons, exec_checkpoint_local, cons, exec_checkpoint_local,
        cons, nil, exec_checkpoint_local]

/-- **THE ZERO-ITERATION SEARCH**: when the low leaf already closes the
window (`nextValue = 0` or `nextValue ≥ _value`), the search loop exits on
its first pass with the evm untouched — the post never runs, and the store
gains exactly the loop scratch `"_3" ↦ NV`, `"expr" ↦ 0`. -/
theorem searchLoop_zero
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {LM V NV : Literal}
    (hlm : (Ok evm σ)["var_lowLeaf_mpos"]!! = LM)
    (hv : (Ok evm σ)["value0"]!! = V)
    (hnv : evm.mload (LM + 64) = NV)
    (hwin : NV = 0 ∨ ¬ (NV < V)) :
    exec (fuel+1+1+1) searchLoopFor (Ok evm σ)
      = Ok evm (Finmap.insert "expr" 0 (Finmap.insert "_3" NV σ)) := by
  show exec (Nat.succ (Nat.succ (fuel+1))) searchLoopFor (Ok evm σ)
      = Ok evm (Finmap.insert "expr" 0 (Finmap.insert "_3" NV σ))
  unfold searchLoopFor
  rw [For']
  dsimp only
  simp only [eval, Lit', mkOk_of_isOk (show isOk (Ok evm σ) from trivial)]
  rw [if_neg (by decide : ¬ ((1 : UInt256) = 0))]
  rw [searchBody_break hlm hv hnv hwin]
  dsimp only
  rw [show (🧟 (Checkpoint (.Break evm
        (Finmap.insert "expr" 0 (Finmap.insert "_3" NV σ)))) : State)
      = Ok evm (Finmap.insert "expr" 0 (Finmap.insert "_3" NV σ)) from rfl]
  simp only [overwrite?_of_Ok]

/-! ### The updateLeaf interleave: `pop(updateLeaf_5205(lowIdx, hashLeaf(ptr)))` -/

/-- The retargeted low leaf's tree update, source-verbatim. -/
@[reducible] def updateInterleaveStmt : Stmt := <s
  pop(fun_updateLeaf_5205(var_lowLeafIndex, fun_hashLeaf(expr_mpos)))
>

/-- **UpdateLeaf-interleave closed form**: hash the staged struct
(`hashLeafOut`), run the level-0 write + Merkle walk on the hash-threaded
state, discard the returned root.  Store untouched. -/
theorem updateInterleave_arm
    {evm : EVMState} {σ : VarStore} {fuel k : ℕ} {IX PTR : Literal}
    (hix : (Ok evm σ)["var_lowLeafIndex"]!! = IX)
    (hptr : (Ok evm σ)["expr_mpos"]!! = PTR)
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hsub0 : (hashLeafOut evm PTR).2.sload 1 ≠ 0)
    (hle : ¬ (IX > (hashLeafOut evm PTR).2.sload 1 - 1))
    (hne2 : (hashLeafOut evm PTR).2.sload 2 ≠ 0)
    (hbidx : IX < (arrOut (hashLeafOut evm PTR).2 2).2.sload
        (arrOut (hashLeafOut evm PTR).2 2).1)
    (hk : ((leafWriteEvm (hashLeafOut evm PTR).2 0 IX
        (hashLeafOut evm PTR).1).sload 0).val = k)
    (hpass : ∀ j, j < k → WalkOK 0 2
        (updateWalk 0 2 j (leafWriteEvm (hashLeafOut evm PTR).2 0 IX
            (hashLeafOut evm PTR).1) 0 IX
          ((hashLeafOut evm PTR).2.sload 1 - 1) (hashLeafOut evm PTR).1))
    (hssinv : ∀ j, j ≤ k →
        ((updateWalk 0 2 j (leafWriteEvm (hashLeafOut evm PTR).2 0 IX
            (hashLeafOut evm PTR).1) 0 IX
          ((hashLeafOut evm PTR).2.sload 1 - 1) (hashLeafOut evm PTR).1).1).sload 0
          = (leafWriteEvm (hashLeafOut evm PTR).2 0 IX
              (hashLeafOut evm PTR).1).sload 0)
    (hfuel : 2 * k + 2 ≤ fuel) :
    exec (fuel+1) updateInterleaveStmt (Ok evm σ)
      = Ok (updateWalk 0 2 k (leafWriteEvm (hashLeafOut evm PTR).2 0 IX
            (hashLeafOut evm PTR).1) 0 IX
          ((hashLeafOut evm PTR).2.sload 1 - 1) (hashLeafOut evm PTR).1).1 σ := by
  unfold updateInterleaveStmt
  rw [ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMPop',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [hptr]
  rw [hashLeaf_vcall hp]
  try simp only [List.head!]
  try simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMPop',
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [lookup_ok_evm_local _ evm, hix]
  rw [updateLeaf_5205_vcall hsub0 hle hne2 hbidx hk hpass hssinv hfuel]
  try simp only [List.head!]
  try simp only [multifill_cons, multifill_nil, EVMPop']

/-- The final push statement, source-verbatim. -/
@[reducible] def pushInterleaveStmt : Stmt := <s
  let var_newRoot := fun_pushNewLeaf(fun_hashLeaf(expr_mpos_1))
>

/-! ### The pushNewLeaf interleave: `let var_newRoot := pushNewLeaf(hashLeaf(ptr))` -/

/-- The hash-threaded entry state of the final push. -/
@[reducible] def pushEH (evm : EVMState) (PTR : UInt256) : EVMState :=
  (hashLeafOut evm PTR).2

/-- The pushed leaf hash. -/
@[reducible] def pushHL (evm : EVMState) (PTR : UInt256) : UInt256 :=
  (hashLeafOut evm PTR).1

/-- **PushNewLeaf-interleave closed form**: hash the new-leaf struct, then
P5's full push (count bump, frontier pad, level-0 write, root walk) on the
hash-threaded state; the new root lands in `var_newRoot`. -/
theorem pushInterleave_arm
    {evm : EVMState} {σ : VarStore} {fuel k k2 : ℕ} {PTR : Literal}
    (hptr : (Ok evm σ)["expr_mpos_1"]!! = PTR)
    (hp : ((evm.mload 64)).val + 128 ≤ 18446744073709551615)
    (hcmax : (pushEH evm PTR).sload 1
      ≠ (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256))
    (hc0 : (pushEH evm PTR).sload 1 ≠ 0)
    (hnp : ¬ ((pushEH evm PTR).sload 1
      = Fin.shiftLeft 1 (((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)).sload 0)))
    -- the padding pack (over the post-increment (pushEH evm PTR))
    (hcont : ∀ j, j < k →
      (padWalk j ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).2.1
          < (padWalk j ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1.sload 0
        ∧ (padWalk j ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).2.2.1
          ≠ (padWalk j ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).2.2.2)
    (hstop : ¬ ((padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).2.1
          < (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1.sload 0)
      ∨ (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).2.2.1
          = (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).2.2.2)
    (hpass : ∀ j, j < k →
      PadOK (padWalk j ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)))
    -- the updateLeaf pack (over the post-padding (pushEH evm PTR))
    (hsub0 : (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1.sload
        ((0 : UInt256) + 1) ≠ 0)
    (hle : ¬ ((pushEH evm PTR).sload 1
      > (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1.sload
          ((0 : UInt256) + 1) - 1))
    (hne2 : (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1.sload
        ((0 : UInt256) + 2) ≠ 0)
    (hbidx : (pushEH evm PTR).sload 1
      < (arrOut (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1
            ((0 : UInt256) + 2)).2.sload
          (arrOut (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1
            ((0 : UInt256) + 2)).1)
    (hk2 : ((leafWriteEvm
        (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1
        0 ((pushEH evm PTR).sload 1) (pushHL evm PTR)).sload 0).val = k2)
    (hpass2 : ∀ j, j < k2 → WalkOK 0 ((0 : UInt256) + 2)
        (updateWalk 0 ((0 : UInt256) + 2) j
          (leafWriteEvm
            (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1
            0 ((pushEH evm PTR).sload 1) (pushHL evm PTR))
          0 ((pushEH evm PTR).sload 1)
          ((padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1.sload
            ((0 : UInt256) + 1) - 1) (pushHL evm PTR)))
    (hssinv2 : ∀ j, j ≤ k2 →
        ((updateWalk 0 ((0 : UInt256) + 2) j
          (leafWriteEvm
            (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1
            0 ((pushEH evm PTR).sload 1) (pushHL evm PTR))
          0 ((pushEH evm PTR).sload 1)
          ((padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1.sload
            ((0 : UInt256) + 1) - 1) (pushHL evm PTR)).1).sload 0
          = (leafWriteEvm
              (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1
              0 ((pushEH evm PTR).sload 1) (pushHL evm PTR)).sload 0)
    (hfuelp : 2 * k + 2 ≤ fuel)
    (hfuelu : 2 * k2 + 2 ≤ fuel) :

    exec (fuel+1) pushInterleaveStmt (Ok evm σ)
      = Ok (updateWalk 0 ((0 : UInt256) + 2) k2
            (leafWriteEvm
              (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1
              0 ((pushEH evm PTR).sload 1) (pushHL evm PTR))
            0 ((pushEH evm PTR).sload 1)
            ((padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1.sload
              ((0 : UInt256) + 1) - 1) (pushHL evm PTR)).1
          (σ.insert "var_newRoot"
            (updateWalk 0 ((0 : UInt256) + 2) k2
              (leafWriteEvm
                (padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1
                0 ((pushEH evm PTR).sload 1) (pushHL evm PTR))
              0 ((pushEH evm PTR).sload 1)
              ((padWalk k ((pushEH evm PTR).sstore 1 ((pushEH evm PTR).sload 1 + 1)) 0 ((pushEH evm PTR).sload 1 - 1) ((pushEH evm PTR).sload 1)).1.sload
                ((0 : UInt256) + 1) - 1) (pushHL evm PTR)).2.2.2.2)  := by
  unfold pushInterleaveStmt
  rw [LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil,
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [hptr]
  rw [hashLeaf_vcall hp]
  try simp only [List.head!]
  try simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil,
             evm_Ok, setEvm_Ok, insert_Ok]
  rw [pushNewLeaf_call hcmax hc0 hnp hcont hstop hpass hsub0 hle hne2 hbidx
      hk2 hpass2 hssinv2 hfuelp hfuelu]
/-! ### The remaining small guards of the insert glue -/

/-- The tree-initialized guard (`0x57243cc5 = 1461992645`): the leaf count
must be nonzero — genesis exists. -/
@[reducible] def initGuardIf : Stmt := <s
  if iszero(_1)
  {
      mstore(0, shl(225, 1461992645))
      revert(0, 4)
  }
>

theorem insert_init_pass
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {X : Literal}
    (hx : (Ok evm σ)["_1"]!! = X)
    (hnz : X ≠ 0) :
    exec (fuel+1) initGuardIf (Ok evm σ) = Ok evm σ := by
  unfold initGuardIf
  rw [If']
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', evm_Ok]
  rw [hx]
  try simp only [List.head!]
  simp only [show (decide (X = 0)) = false from decide_eq_false hnz]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  rw [if_neg (by exact fun h => h rfl)]

theorem insert_init_reverts
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    (hx : (Ok evm σ)["_1"]!! = 0) :
    (exec (fuel+1) initGuardIf (Ok evm σ)).evm.reverted = true := by
  unfold initGuardIf
  rw [If']
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', evm_Ok]
  rw [hx]
  try simp only [List.head!]
  try simp only [show (decide ((0 : UInt256) = 0)) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  try simp only [show fromBool (decide True) = (1 : UInt256) from by decide]
  rw [if_pos (by decide : (1 : UInt256) ≠ 0)]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMShl', EVMMstore', evm_Ok, setEvm_Ok]
  try simp only [List.head!]
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMRevert', evm_Ok, setEvm_Ok]
  rfl

/-- The nonzero-value guard (`0xbd1de53d = 3172853053`): zero is the genesis
key and can never be inserted. -/
@[reducible] def valueZeroGuardIf : Stmt := <s
  if iszero(value0)
  {
      mstore(0, shl(224, 3172853053))
      revert(0, 4)
  }
>

theorem insert_valueZero_pass
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {X : Literal}
    (hx : (Ok evm σ)["value0"]!! = X)
    (hnz : X ≠ 0) :
    exec (fuel+1) valueZeroGuardIf (Ok evm σ) = Ok evm σ := by
  unfold valueZeroGuardIf
  rw [If']
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', evm_Ok]
  rw [hx]
  try simp only [List.head!]
  simp only [show (decide (X = 0)) = false from decide_eq_false hnz]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  rw [if_neg (by exact fun h => h rfl)]

theorem insert_valueZero_reverts
    {evm : EVMState} {σ : VarStore} {fuel : ℕ}
    (hx : (Ok evm σ)["value0"]!! = 0) :
    (exec (fuel+1) valueZeroGuardIf (Ok evm σ)).evm.reverted = true := by
  unfold valueZeroGuardIf
  rw [If']
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', evm_Ok]
  rw [hx]
  try simp only [List.head!]
  try simp only [show (decide ((0 : UInt256) = 0)) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  try simp only [show fromBool (decide True) = (1 : UInt256) from by decide]
  rw [if_pos (by decide : (1 : UInt256) ≠ 0)]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMShl', EVMMstore', evm_Ok, setEvm_Ok]
  try simp only [List.head!]
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMRevert', evm_Ok, setEvm_Ok]
  rfl

/-- The index-bounds guard (`0x037dc2ed = 58573549`): the candidate window
index must be below the leaf count. -/
@[reducible] def boundsGuardIf : Stmt := <s
  if iszero(lt(value1, _1))
  {
      mstore(0, shl(224, 58573549))
      revert(0, abi_encode_uint256_uint256(value1, _1))
  }
>

theorem insert_bounds_pass
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {IX C : Literal}
    (hix : (Ok evm σ)["value1"]!! = IX)
    (hc : (Ok evm σ)["_1"]!! = C)
    (hlt : IX < C) :
    exec (fuel+1) boundsGuardIf (Ok evm σ) = Ok evm σ := by
  unfold boundsGuardIf
  rw [If']
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMLt', evm_Ok]
  rw [hix, hc]
  try simp only [List.head!]
  simp only [show decide (IX < C) = true from decide_eq_true hlt]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  try simp only [show fromBool (decide True) = (1 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  rw [if_neg (by exact fun h => h rfl)]

theorem insert_bounds_reverts
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {IX C : Literal}
    (hix : (Ok evm σ)["value1"]!! = IX)
    (hc : (Ok evm σ)["_1"]!! = C)
    (hge : ¬ (IX < C)) :
    (exec (fuel+1) boundsGuardIf (Ok evm σ)).evm.reverted = true := by
  unfold boundsGuardIf
  rw [If']
  simp only [eval, evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMIszero', EVMLt', evm_Ok]
  rw [hix, hc]
  try simp only [List.head!]
  simp only [show decide (IX < C) = false from decide_eq_false hge]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  try simp only [show fromBool (decide True) = (1 : UInt256) from by decide]
  rw [if_pos (by decide : (1 : UInt256) ≠ 0)]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMShl', EVMMstore', evm_Ok, setEvm_Ok]
  try simp only [List.head!]
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', Call', evalCall, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMRevert', evm_Ok, setEvm_Ok]
  rw [lookup_ok_evm_local _ evm, hix]
  rw [lookup_ok_evm_local _ evm, hc]
  rw [abi_encode_uint256_uint256_call]
  try simp only [List.head!]
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil,
             EVMRevert', evm_Ok, setEvm_Ok]
  rfl

/-! ### The guards-stage join of the insert glue

The dispatcher glue from the appender gate through the low-leaf search
loop, as ONE cons-composition over a generic tail `rest` (the style of
`executeCalls_step_guards`).  Store-tower derivation, step by step:

```
  entry                     Ok evm σ
  appenderIf     (pure)     Ok evm σ
  let _1 := sload(1)        Ok evm σ₁,  σ₁ = σ.insert "_1" (evm.sload 1)
  initGuardIf    (pure)     Ok evm σ₁       (tests the ORIGINAL count _1 —
                                             bound BEFORE the dedup threading)
  valueZeroGuardIf (pure)   Ok evm σ₁
  dedupIf        (threads)  Ok E₁ σ₁,   E₁ = (accOut evm V 5).2
  boundsGuardIf  (pure)     Ok E₁ σ₁
  lowLeafReadChunk (threads) Ok E₂ σ₄,
      LM = (accOut E₁ IX 4).2.mload 64
      E₂ = leafReadEvm (accOut E₁ IX 4).2 (accOut E₁ IX 4).1
      σ₄ = ((σ₁.insert "var_lowLeafIndex" IX).insert
             "var_lowLeaf_mpos" LM).insert "_2" (E₂.mload LM)
  valueOrderIf   (pure)     Ok E₂ σ₄
  let var_attempts := 0     Ok E₂ σ₅,   σ₅ = σ₄.insert "var_attempts" 0
  searchLoopFor  (0 iter)   Ok E₂ (insert "expr" 0
                                    (insert "_3" (E₂.mload (LM+64)) σ₅))
```
-/

/-- The leaf-count loader of the insert glue, source-verbatim (yul 159). -/
@[reducible] def glueLet1 : Stmt := <s let _1 := sload(1)>

/-- The search-attempt counter init, source-verbatim (yul 207). -/
@[reducible] def glueLetAttempts : Stmt := <s let var_attempts := 0>

open Clear.KeccakDeterminism in
/-- **THE GUARDS-STAGE JOIN of the insert glue**: for an AFM-sent, fresh,
nonzero value inserted against an in-bounds low leaf whose window already
closes, the glue drives deterministically from the dispatcher entry through
the search loop.  The evm threads exactly twice (the dedup accessor's
keccak step, then the leaves accessor + struct read), and the store gains
exactly the seven glue scratch bindings.  Generic in the remaining
statement list `rest`. -/
theorem insertGlue_guards
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {V IX : Literal}
    {rest : List Stmt}
    (hv0 : (Ok evm σ)["value0"]!! = V)
    (hv1 : (Ok evm σ)["value1"]!! = IX)
    (hcaller : evm.execution_env.source = (65556 : UInt256))
    (h1nz : evm.sload 1 ≠ 0)
    (hvnz : V ≠ 0)
    (hz : (accOut evm V 5).2.sload ((accOut evm V 5).1) = 0)
    (hbound : IX < evm.sload 1)
    (hp : (((accOut (accOut evm V 5).2 IX 4).2).mload 64).val + 96
        ≤ 18446744073709551615)
    (hvo : (leafReadEvm (accOut (accOut evm V 5).2 IX 4).2
          (accOut (accOut evm V 5).2 IX 4).1).mload
          ((accOut (accOut evm V 5).2 IX 4).2.mload 64) < V)
    (hwin : (leafReadEvm (accOut (accOut evm V 5).2 IX 4).2
          (accOut (accOut evm V 5).2 IX 4).1).mload
          ((accOut (accOut evm V 5).2 IX 4).2.mload 64 + 64) = 0
        ∨ ¬ ((leafReadEvm (accOut (accOut evm V 5).2 IX 4).2
          (accOut (accOut evm V 5).2 IX 4).1).mload
          ((accOut (accOut evm V 5).2 IX 4).2.mload 64 + 64) < V)) :
    exec (fuel+1+1+1) (Stmt.Block (appenderIf :: glueLet1 :: initGuardIf ::
        valueZeroGuardIf :: dedupIf :: boundsGuardIf :: lowLeafReadChunk ::
        valueOrderIf :: glueLetAttempts :: searchLoopFor :: rest)) (Ok evm σ)
      = exec (fuel+1+1+1) (Stmt.Block rest)
          (Ok (leafReadEvm (accOut (accOut evm V 5).2 IX 4).2
                (accOut (accOut evm V 5).2 IX 4).1)
            (Finmap.insert "expr" 0 (Finmap.insert "_3"
              ((leafReadEvm (accOut (accOut evm V 5).2 IX 4).2
                (accOut (accOut evm V 5).2 IX 4).1).mload
                ((accOut (accOut evm V 5).2 IX 4).2.mload 64 + 64))
              (((((σ.insert "_1" (evm.sload 1)).insert
                "var_lowLeafIndex" IX).insert
                "var_lowLeaf_mpos" ((accOut (accOut evm V 5).2 IX 4).2.mload 64)).insert
                "_2" ((leafReadEvm (accOut (accOut evm V 5).2 IX 4).2
                  (accOut (accOut evm V 5).2 IX 4).1).mload
                  ((accOut (accOut evm V 5).2 IX 4).2.mload 64))).insert
                "var_attempts" 0)))) := by
  -- appender gate: pure pass
  rw [cons]
  rw [insert_appender_pass (fuel := fuel+1+1) hcaller]
  -- let _1 := sload(1): bind the ORIGINAL leaf count
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             multifill_cons, multifill_nil, EVMSload',
             evm_Ok, setEvm_Ok, insert_Ok]
  -- init guard: the original count is nonzero
  rw [cons]
  rw [insert_init_pass (fuel := fuel+1+1) (X := evm.sload 1)
    lookup_insert_self_local h1nz]
  -- nonzero-value guard
  rw [cons]
  rw [insert_valueZero_pass (fuel := fuel+1+1) (X := V)
    (by rw [lookup_insert_ne_fin_local (by decide)]
        exact hv0)
    hvnz]
  -- dedup gate: threads the valueToIndex accessor (accOut … 5)
  rw [cons]
  rw [insert_dedup_pass (fuel := fuel+1+1) (V := V)
    (by rw [lookup_insert_ne_fin_local (by decide)]
        exact hv0)
    hz]
  -- bounds guard (pure, over the accOut-threaded evm)
  rw [cons]
  rw [insert_bounds_pass (fuel := fuel+1+1) (IX := IX) (C := evm.sload 1)
    (by rw [lookup_insert_ne_fin_local (by decide), lookup_ok_evm_local _ evm]
        exact hv1)
    lookup_insert_self_local
    hbound]
  -- low-leaf read chunk: threads accOut … 4 + leafReadEvm
  rw [cons]
  rw [lowLeafRead_arm (fuel := fuel+1+1) (IX := IX)
    (by rw [lookup_insert_ne_fin_local (by decide), lookup_ok_evm_local _ evm]
        exact hv1)
    hp]
  -- value-order guard (pure, over the read state)
  rw [cons]
  rw [valueOrder_pass (fuel := fuel+1+1)
    (L := (leafReadEvm (accOut (accOut evm V 5).2 IX 4).2
        (accOut (accOut evm V 5).2 IX 4).1).mload
        ((accOut (accOut evm V 5).2 IX 4).2.mload 64))
    (V := V)
    lookup_insert_self_local
    (by rw [lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_ok_evm_local _ evm]
        exact hv0)
    hvo]
  -- let var_attempts := 0
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  -- the zero-iteration search loop (the fuel+3 arm: fuel := fuel)
  rw [cons]
  rw [searchLoop_zero (fuel := fuel)
    (LM := (accOut (accOut evm V 5).2 IX 4).2.mload 64)
    (V := V)
    (NV := (leafReadEvm (accOut (accOut evm V 5).2 IX 4).2
        (accOut (accOut evm V 5).2 IX 4).1).mload
        ((accOut (accOut evm V 5).2 IX 4).2.mload 64 + 64))
    (by rw [lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide)]
        exact lookup_insert_self_local)
    (by rw [lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_ok_evm_local _ evm]
        exact hv0)
    rfl
    hwin]

/-! ### The writes-stage join of the insert glue

The four mutation arms — retarget staging, the low-leaf tree update, the
new-leaf staging + registration, and the final push — as ONE
cons-composition over a generic tail `rest`.  Evm/store tower:

```
  entry              Ok evm σ
  retargetChunk      Ok RS σ_r,  RS  = retargetStageEvm evm LM NI V IX
                                 σ_r = σ + {_4, _5, _6, expr_mpos}
  updateInterleave   Ok UW σ_r,  UW  = insertUpdEvm evm LM NI V IX k
  newLeafChunk       Ok NL σ_p,  NL  = insertNewEvm evm LM NI V IX k
                                 σ_p = σ_r + {expr_mpos_1 ↦ UW.mload 64}
  pushInterleave     Ok (pushOutW NL (UW.mload 64) k2 k3).1
                        (σ_p + {var_newRoot ↦ (pushOutW …).2.2.2.2})
```
-/

/-- The updateLeaf walk tuple over a staged entry `E` (struct at `P`,
target index `IX`, `j` walk levels): hash the struct, level-0 write of the
hash at `IX`, `j` walk steps toward `count − 1`.  `.1` is the threaded
evm. -/
@[reducible] def updTreeW (E : EVMState) (P IX : UInt256) (j : ℕ) :=
  updateWalk 0 2 j
    (leafWriteEvm (hashLeafOut E P).2 0 IX (hashLeafOut E P).1) 0 IX
    ((hashLeafOut E P).2.sload 1 - 1) (hashLeafOut E P).1

/-- The evm after retargetChunk + updateInterleave (writes stage 2). -/
@[reducible] def insertUpdEvm (evm : EVMState) (LM NI V IX : UInt256) (k : ℕ) : EVMState :=
  (updTreeW (retargetStageEvm evm LM NI V IX) (evm.mload 64) IX k).1

/-- The evm after newLeafChunk (writes stage 3). -/
@[reducible] def insertNewEvm (evm : EVMState) (LM NI V IX : UInt256) (k : ℕ) : EVMState :=
  newLeafStageEvm (insertUpdEvm evm LM NI V IX k) V
    (evm.mload (LM + 32)) (evm.mload (LM + 64)) NI

/-- The push pad-walk tuple over a push-entry state `E` (new-leaf struct at
`P`, `j` pad levels) — P5's frontier padding on the post-increment state. -/
@[reducible] def pushPadW (E : EVMState) (P : UInt256) (j : ℕ) :=
  padWalk j ((pushEH E P).sstore 1 ((pushEH E P).sload 1 + 1)) 0
    ((pushEH E P).sload 1 - 1) ((pushEH E P).sload 1)

/-- The push update-walk tuple after `k` pad levels: level-0 write of the
pushed hash at the old count, then `j` walk levels.  `.1` is the final evm,
`.2.2.2.2` the returned root. -/
@[reducible] def pushOutW (E : EVMState) (P : UInt256) (k j : ℕ) :=
  updateWalk 0 ((0 : UInt256) + 2) j
    (leafWriteEvm (pushPadW E P k).1 0 ((pushEH E P).sload 1) (pushHL E P))
    0 ((pushEH E P).sload 1)
    ((pushPadW E P k).1.sload ((0 : UInt256) + 1) - 1) (pushHL E P)

/-- **THE WRITES-STAGE JOIN of the insert glue**: from the post-guards
entry, the four mutation arms drive deterministically — retarget staging,
the low-leaf tree update (`k` walk levels), new-leaf staging +
registration, and the final push (`k2` pad levels, `k3` walk levels).  The
store gains exactly the four staging scratch bindings and the new root.
Generic in the remaining statement list `rest`. -/
theorem insertGlue_writes
    {evm : EVMState} {σ : VarStore} {fuel k k2 k3 : ℕ} {LM NI V IX : Literal}
    {rest : List Stmt}
    (hlm : (Ok evm σ)["var_lowLeaf_mpos"]!! = LM)
    (h1 : (Ok evm σ)["_1"]!! = NI)
    (hv : (Ok evm σ)["value0"]!! = V)
    (hix : (Ok evm σ)["var_lowLeafIndex"]!! = IX)
    (hp : (evm.mload 64).val + 96 ≤ 18446744073709551615)
    -- the updateLeaf-interleave pack (over the retarget-staged evm)
    (hpU : ((retargetStageEvm evm LM NI V IX).mload 64).val + 128
        ≤ 18446744073709551615)
    (hsub0U : (hashLeafOut (retargetStageEvm evm LM NI V IX) (evm.mload 64)).2.sload 1 ≠ 0)
    (hleU : ¬ (IX > (hashLeafOut (retargetStageEvm evm LM NI V IX) (evm.mload 64)).2.sload 1 - 1))
    (hne2U : (hashLeafOut (retargetStageEvm evm LM NI V IX) (evm.mload 64)).2.sload 2 ≠ 0)
    (hbidxU : IX < (arrOut (hashLeafOut (retargetStageEvm evm LM NI V IX) (evm.mload 64)).2 2).2.sload
        (arrOut (hashLeafOut (retargetStageEvm evm LM NI V IX) (evm.mload 64)).2 2).1)
    (hkU : ((leafWriteEvm (hashLeafOut (retargetStageEvm evm LM NI V IX) (evm.mload 64)).2 0 IX
        (hashLeafOut (retargetStageEvm evm LM NI V IX) (evm.mload 64)).1).sload 0).val = k)
    (hpassU : ∀ j, j < k → WalkOK 0 2
        (updTreeW (retargetStageEvm evm LM NI V IX) (evm.mload 64) IX j))
    (hssinvU : ∀ j, j ≤ k →
        ((updTreeW (retargetStageEvm evm LM NI V IX) (evm.mload 64) IX j).1).sload 0
          = (leafWriteEvm (hashLeafOut (retargetStageEvm evm LM NI V IX) (evm.mload 64)).2 0 IX
              (hashLeafOut (retargetStageEvm evm LM NI V IX) (evm.mload 64)).1).sload 0)
    (hfuelU : 2 * k + 2 ≤ fuel + 1 + 1)
    -- the new-leaf allocator bound (over the updated-tree evm)
    (hpN : ((insertUpdEvm evm LM NI V IX k).mload 64).val + 96 ≤ 18446744073709551615)
    -- the P5 push pack (over the new-leaf-staged evm)
    (hpP : ((insertNewEvm evm LM NI V IX k).mload 64).val + 128 ≤ 18446744073709551615)
    (hcmax : (pushEH (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64)).sload 1
      ≠ (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256))
    (hc0 : (pushEH (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64)).sload 1 ≠ 0)
    (hnp : ¬ ((pushEH (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64)).sload 1
      = Fin.shiftLeft 1
          (((pushEH (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64)).sstore 1
            ((pushEH (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64)).sload 1 + 1)).sload 0)))
    (hcont : ∀ j, j < k2 →
      (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) j).2.1
          < (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) j).1.sload 0
        ∧ (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) j).2.2.1
          ≠ (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) j).2.2.2)
    (hstop : ¬ ((pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) k2).2.1
          < (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) k2).1.sload 0)
      ∨ (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) k2).2.2.1
          = (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) k2).2.2.2)
    (hpassP : ∀ j, j < k2 →
      PadOK (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) j))
    (hsub0P : (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) k2).1.sload
        ((0 : UInt256) + 1) ≠ 0)
    (hleP : ¬ ((pushEH (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64)).sload 1
      > (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) k2).1.sload
          ((0 : UInt256) + 1) - 1))
    (hne2P : (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) k2).1.sload
        ((0 : UInt256) + 2) ≠ 0)
    (hbidxP : (pushEH (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64)).sload 1
      < (arrOut (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) k2).1
            ((0 : UInt256) + 2)).2.sload
          (arrOut (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) k2).1
            ((0 : UInt256) + 2)).1)
    (hk2P : ((leafWriteEvm
        (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) k2).1
        0 ((pushEH (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64)).sload 1)
        (pushHL (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64))).sload 0).val = k3)
    (hpass2 : ∀ j, j < k3 → WalkOK 0 ((0 : UInt256) + 2)
        (pushOutW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) k2 j))
    (hssinv2 : ∀ j, j ≤ k3 →
        ((pushOutW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) k2 j).1).sload 0
          = (leafWriteEvm
              (pushPadW (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64) k2).1
              0 ((pushEH (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64)).sload 1)
              (pushHL (insertNewEvm evm LM NI V IX k) ((insertUpdEvm evm LM NI V IX k).mload 64))).sload 0)
    (hfuelP : 2 * k2 + 2 ≤ fuel + 1 + 1)
    (hfuelP2 : 2 * k3 + 2 ≤ fuel + 1 + 1) :
    exec (fuel+1+1+1) (Stmt.Block (retargetChunk :: updateInterleaveStmt ::
        newLeafChunk :: pushInterleaveStmt :: rest)) (Ok evm σ)
      = exec (fuel+1+1+1) (Stmt.Block rest)
          (Ok (pushOutW (insertNewEvm evm LM NI V IX k)
                ((insertUpdEvm evm LM NI V IX k).mload 64) k2 k3).1
            ((((((σ.insert "_4" (evm.mload (LM + 32))).insert
              "_5" (evm.mload (LM + 64))).insert
              "_6" (evm.mload LM)).insert
              "expr_mpos" (evm.mload 64)).insert
              "expr_mpos_1" ((insertUpdEvm evm LM NI V IX k).mload 64)).insert
              "var_newRoot" (pushOutW (insertNewEvm evm LM NI V IX k)
                ((insertUpdEvm evm LM NI V IX k).mload 64) k2 k3).2.2.2.2)) := by
  -- retarget staging
  rw [cons]
  rw [retargetStage_arm (fuel := fuel+1+1) (LM := LM) (NI := NI) (V := V) (IX := IX)
    hlm h1 hv hix hp]
  -- the low-leaf tree update
  rw [cons]
  rw [updateInterleave_arm (fuel := fuel+1+1) (k := k)
    (evm := retargetStageEvm evm LM NI V IX) (IX := IX) (PTR := evm.mload 64)
    (by rw [lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_ok_evm_local _ evm]
        exact hix)
    lookup_insert_self_local
    hpU hsub0U hleU hne2U hbidxU hkU hpassU hssinvU hfuelU]
  -- new-leaf staging + registration
  rw [cons]
  rw [newLeafStage_arm (fuel := fuel+1+1)
    (evm := insertUpdEvm evm LM NI V IX k) (V := V)
    (NI4 := evm.mload (LM + 32)) (NV5 := evm.mload (LM + 64)) (IX1 := NI)
    (by rw [lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_ok_evm_local _ evm]
        exact hv)
    (by rw [lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide)]
        exact lookup_insert_self_local)
    (by rw [lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide)]
        exact lookup_insert_self_local)
    (by rw [lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_ok_evm_local _ evm]
        exact h1)
    hpN]
  -- the final push
  rw [cons]
  rw [pushInterleave_arm (fuel := fuel+1+1) (k := k2) (k2 := k3)
    (evm := insertNewEvm evm LM NI V IX k)
    (PTR := (insertUpdEvm evm LM NI V IX k).mload 64)
    lookup_insert_self_local
    hpP hcmax hc0 hnp hcont hstop hpassP hsub0P hleP hne2P hbidxP hk2P
    hpass2 hssinv2 hfuelP hfuelP2]

/-! ### The full prefix join: guards + writes -/

open Clear.KeccakDeterminism in
/-- The guards' final threaded evm (dedup keccak step, leaves keccak step,
low-leaf struct materialization). -/
@[reducible] def guardsEvm (evm : EVMState) (V IX : UInt256) : EVMState :=
  leafReadEvm (accOut (accOut evm V 5).2 IX 4).2 (accOut (accOut evm V 5).2 IX 4).1

open Clear.KeccakDeterminism in
/-- The guards' low-leaf struct pointer (the free pointer of the
accessor-threaded evm). -/
@[reducible] def guardsLM (evm : EVMState) (V IX : UInt256) : UInt256 :=
  (accOut (accOut evm V 5).2 IX 4).2.mload 64

open Clear.KeccakDeterminism in
/-- **THE FULL PREFIX JOIN of the insert glue**: guards stage + writes
stage.  For an AFM-sent, fresh, nonzero value inserted against an in-bounds
low leaf whose window already closes, the dispatcher glue drives
deterministically from entry through the final push: the seven guard
bindings, the four staging bindings, and the new root land in the store;
the evm threads the two accessor keccak steps, the retarget staging + tree
update, the new-leaf staging + registration, and the push (pad + walk).
Generic in the remaining statement list `rest`. -/
theorem insertGlue_prefix
    {evm : EVMState} {σ : VarStore} {fuel k k2 k3 : ℕ} {V IX : Literal}
    {rest : List Stmt}
    (hv0 : (Ok evm σ)["value0"]!! = V)
    (hv1 : (Ok evm σ)["value1"]!! = IX)
    (hcaller : evm.execution_env.source = (65556 : UInt256))
    (h1nz : evm.sload 1 ≠ 0)
    (hvnz : V ≠ 0)
    (hz : (accOut evm V 5).2.sload ((accOut evm V 5).1) = 0)
    (hbound : IX < evm.sload 1)
    (hpG : (((accOut (accOut evm V 5).2 IX 4).2).mload 64).val + 96
        ≤ 18446744073709551615)
    (hvo : (leafReadEvm (accOut (accOut evm V 5).2 IX 4).2
          (accOut (accOut evm V 5).2 IX 4).1).mload
          ((accOut (accOut evm V 5).2 IX 4).2.mload 64) < V)
    (hwin : (leafReadEvm (accOut (accOut evm V 5).2 IX 4).2
          (accOut (accOut evm V 5).2 IX 4).1).mload
          ((accOut (accOut evm V 5).2 IX 4).2.mload 64 + 64) = 0
        ∨ ¬ ((leafReadEvm (accOut (accOut evm V 5).2 IX 4).2
          (accOut (accOut evm V 5).2 IX 4).1).mload
          ((accOut (accOut evm V 5).2 IX 4).2.mload 64 + 64) < V))
    -- the writes-stage packs, over the guards' final threaded evm
    (hpW : ((guardsEvm evm V IX).mload 64).val + 96 ≤ 18446744073709551615)
    (hpU : ((retargetStageEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX).mload 64).val + 128
        ≤ 18446744073709551615)
    (hsub0U : (hashLeafOut (retargetStageEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX)
        ((guardsEvm evm V IX).mload 64)).2.sload 1 ≠ 0)
    (hleU : ¬ (IX > (hashLeafOut (retargetStageEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX)
        ((guardsEvm evm V IX).mload 64)).2.sload 1 - 1))
    (hne2U : (hashLeafOut (retargetStageEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX)
        ((guardsEvm evm V IX).mload 64)).2.sload 2 ≠ 0)
    (hbidxU : IX < (arrOut (hashLeafOut (retargetStageEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX)
          ((guardsEvm evm V IX).mload 64)).2 2).2.sload
        (arrOut (hashLeafOut (retargetStageEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX)
          ((guardsEvm evm V IX).mload 64)).2 2).1)
    (hkU : ((leafWriteEvm (hashLeafOut (retargetStageEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX)
          ((guardsEvm evm V IX).mload 64)).2 0 IX
        (hashLeafOut (retargetStageEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX)
          ((guardsEvm evm V IX).mload 64)).1).sload 0).val = k)
    (hpassU : ∀ j, j < k → WalkOK 0 2
        (updTreeW (retargetStageEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX)
          ((guardsEvm evm V IX).mload 64) IX j))
    (hssinvU : ∀ j, j ≤ k →
        ((updTreeW (retargetStageEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX)
            ((guardsEvm evm V IX).mload 64) IX j).1).sload 0
          = (leafWriteEvm (hashLeafOut (retargetStageEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX)
              ((guardsEvm evm V IX).mload 64)).2 0 IX
            (hashLeafOut (retargetStageEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX)
              ((guardsEvm evm V IX).mload 64)).1).sload 0)
    (hfuelU : 2 * k + 2 ≤ fuel + 1 + 1)
    (hpN : ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64).val + 96
        ≤ 18446744073709551615)
    (hpP : ((insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64).val + 128
        ≤ 18446744073709551615)
    (hcmax : (pushEH (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
        ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64)).sload 1
      ≠ (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256))
    (hc0 : (pushEH (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
        ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64)).sload 1 ≠ 0)
    (hnp : ¬ ((pushEH (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
        ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64)).sload 1
      = Fin.shiftLeft 1
          (((pushEH (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
              ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64)).sstore 1
            ((pushEH (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
              ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64)).sload 1 + 1)).sload 0)))
    (hcont : ∀ j, j < k2 →
      (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
          ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) j).2.1
        < (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
          ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) j).1.sload 0
      ∧ (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
          ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) j).2.2.1
        ≠ (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
          ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) j).2.2.2)
    (hstop : ¬ ((pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
          ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2).2.1
        < (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
          ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2).1.sload 0)
      ∨ (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
          ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2).2.2.1
        = (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
          ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2).2.2.2)
    (hpassP : ∀ j, j < k2 →
      PadOK (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
        ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) j))
    (hsub0P : (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
        ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2).1.sload
        ((0 : UInt256) + 1) ≠ 0)
    (hleP : ¬ ((pushEH (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
        ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64)).sload 1
      > (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
          ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2).1.sload
          ((0 : UInt256) + 1) - 1))
    (hne2P : (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
        ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2).1.sload
        ((0 : UInt256) + 2) ≠ 0)
    (hbidxP : (pushEH (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
        ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64)).sload 1
      < (arrOut (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
            ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2).1
            ((0 : UInt256) + 2)).2.sload
          (arrOut (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
            ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2).1
            ((0 : UInt256) + 2)).1)
    (hk2P : ((leafWriteEvm
        (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
          ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2).1
        0 ((pushEH (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
          ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64)).sload 1)
        (pushHL (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
          ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64))).sload 0).val = k3)
    (hpass2 : ∀ j, j < k3 → WalkOK 0 ((0 : UInt256) + 2)
        (pushOutW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
          ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2 j))
    (hssinv2 : ∀ j, j ≤ k3 →
        ((pushOutW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
            ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2 j).1).sload 0
          = (leafWriteEvm
              (pushPadW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
                ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2).1
              0 ((pushEH (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
                ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64)).sload 1)
              (pushHL (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
                ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64))).sload 0)
    (hfuelP : 2 * k2 + 2 ≤ fuel + 1 + 1)
    (hfuelP2 : 2 * k3 + 2 ≤ fuel + 1 + 1) :
    exec (fuel+1+1+1) (Stmt.Block (appenderIf :: glueLet1 :: initGuardIf ::
        valueZeroGuardIf :: dedupIf :: boundsGuardIf :: lowLeafReadChunk ::
        valueOrderIf :: glueLetAttempts :: searchLoopFor ::
        retargetChunk :: updateInterleaveStmt :: newLeafChunk ::
        pushInterleaveStmt :: rest)) (Ok evm σ)
      = exec (fuel+1+1+1) (Stmt.Block rest)
          (Ok (pushOutW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
                ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2 k3).1
            ((((((( Finmap.insert "expr" 0 (Finmap.insert "_3"
                ((guardsEvm evm V IX).mload (guardsLM evm V IX + 64))
                (((((σ.insert "_1" (evm.sload 1)).insert
                  "var_lowLeafIndex" IX).insert
                  "var_lowLeaf_mpos" (guardsLM evm V IX)).insert
                  "_2" ((guardsEvm evm V IX).mload (guardsLM evm V IX))).insert
                  "var_attempts" 0))).insert
              "_4" ((guardsEvm evm V IX).mload (guardsLM evm V IX + 32))).insert
              "_5" ((guardsEvm evm V IX).mload (guardsLM evm V IX + 64))).insert
              "_6" ((guardsEvm evm V IX).mload (guardsLM evm V IX))).insert
              "expr_mpos" ((guardsEvm evm V IX).mload 64)).insert
              "expr_mpos_1" ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64)).insert
              "var_newRoot" (pushOutW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
                ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64) k2 k3).2.2.2.2)) := by
  -- the guards stage
  rw [insertGlue_guards hv0 hv1 hcaller h1nz hvnz hz hbound hpG hvo hwin]
  -- the writes stage, entered at the guards' final state
  rw [insertGlue_writes (fuel := fuel) (k := k) (k2 := k2) (k3 := k3)
    (evm := guardsEvm evm V IX) (LM := guardsLM evm V IX)
    (NI := evm.sload 1) (V := V) (IX := IX)
    (by rw [lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide)]
        exact lookup_insert_self_local)
    (by rw [lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide)]
        exact lookup_insert_self_local)
    (by rw [lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_ok_evm_local _ evm]
        exact hv0)
    (by rw [lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide),
            lookup_insert_ne_fin_local (by decide)]
        exact lookup_insert_self_local)
    hpW hpU hsub0U hleU hne2U hbidxU hkU hpassU hssinvU hfuelU
    hpN hpP hcmax hc0 hnp hcont hstop hpassP hsub0P hleP hne2P hbidxP hk2P
    hpass2 hssinv2 hfuelP hfuelP2]


/-! ## The pool and window properties cross the WELD CHAIN

The deployed insert runs `evm → guardsEvm → retargetStage → hashLeaf → updTree → newLeafStage
→ hashLeaf` before it reaches the states `glueSeq` names `H1` and `H3`.  Every constructor on
that path is a composition of atoms whose transport already exists (`mstore`, `sstore`,
`arrOut`, `accOut`, `keccakOut`, `leafWriteEvm`, `updateWalk`), so all five properties the
derived separation route consumes pass straight through.

With these, a caller of the axiom-free `glueSeq_leafSetOf'_of_config` needs the five facts at
the ENTRY state only -- the twin's hypotheses at `guardsEvm`, `H1` and `H3` all derive. -/

lemma separated_leafReadEvm {σ : EVMState} {slot : UInt256}
    (h : Clear.KeccakSlotSep.Separated σ) :
    Clear.KeccakSlotSep.Separated (leafReadEvm σ slot) :=
  (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore h))))

lemma separated_leafScratchEvm {σ : EVMState} {leaf : UInt256}
    (h : Clear.KeccakSlotSep.Separated σ) :
    Clear.KeccakSlotSep.Separated (leafScratchEvm σ leaf) :=
  (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore h)))))

lemma separated_hashLeafOut {σ : EVMState} {leaf : UInt256}
    (h : Clear.KeccakSlotSep.Separated σ) :
    Clear.KeccakSlotSep.Separated ((hashLeafOut σ leaf).2) :=
  (Clear.KeccakSlotSep.separated_keccakOut (separated_leafScratchEvm h))

lemma separated_pushEH {σ : EVMState} {PTR : UInt256}
    (h : Clear.KeccakSlotSep.Separated σ) :
    Clear.KeccakSlotSep.Separated (pushEH σ PTR) :=
  (separated_hashLeafOut h)

lemma separated_guardsEvm {σ : EVMState} {V IX : UInt256}
    (h : Clear.KeccakSlotSep.Separated σ) :
    Clear.KeccakSlotSep.Separated (guardsEvm σ V IX) :=
  (separated_leafReadEvm (separated_accOut (separated_accOut h)))

lemma separated_retargetStageEvm {σ : EVMState} {LM NI V IX : UInt256}
    (h : Clear.KeccakSlotSep.Separated σ) :
    Clear.KeccakSlotSep.Separated (retargetStageEvm σ LM NI V IX) :=
  (Clear.StorageFrame.separated_sstore (Clear.StorageFrame.separated_sstore (Clear.StorageFrame.separated_sstore (separated_accOut (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore h))))))))

lemma separated_newLeafStageEvm {σ : EVMState} {V NI4 NV5 IX1 : UInt256}
    (h : Clear.KeccakSlotSep.Separated σ) :
    Clear.KeccakSlotSep.Separated (newLeafStageEvm σ V NI4 NV5 IX1) :=
  (Clear.StorageFrame.separated_sstore (separated_accOut (Clear.StorageFrame.separated_sstore (Clear.StorageFrame.separated_sstore (Clear.StorageFrame.separated_sstore (separated_accOut (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore h))))))))))

lemma separated_updTreeW (j : ℕ) {E : EVMState} {P IX : UInt256}
    (h : Clear.KeccakSlotSep.Separated E) :
    Clear.KeccakSlotSep.Separated ((updTreeW E P IX j).1) :=
  (separated_updateWalk j (separated_leafWriteEvm (separated_hashLeafOut h)))

lemma separated_insertUpdEvm (k : ℕ) {σ : EVMState} {LM NI V IX : UInt256}
    (h : Clear.KeccakSlotSep.Separated σ) :
    Clear.KeccakSlotSep.Separated (insertUpdEvm σ LM NI V IX k) :=
  (separated_updTreeW k (separated_retargetStageEvm h))

lemma separated_insertNewEvm (k : ℕ) {σ : EVMState} {LM NI V IX : UInt256}
    (h : Clear.KeccakSlotSep.Separated σ) :
    Clear.KeccakSlotSep.Separated (insertNewEvm σ LM NI V IX k) :=
  (separated_newLeafStageEvm (separated_insertUpdEvm k h))

lemma cacheInUsed_leafReadEvm {σ : EVMState} {slot : UInt256}
    (h : Clear.KeccakFresh.CacheInUsed σ) :
    Clear.KeccakFresh.CacheInUsed (leafReadEvm σ slot) :=
  (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ h))))

lemma cacheInUsed_leafScratchEvm {σ : EVMState} {leaf : UInt256}
    (h : Clear.KeccakFresh.CacheInUsed σ) :
    Clear.KeccakFresh.CacheInUsed (leafScratchEvm σ leaf) :=
  (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ h)))))

lemma cacheInUsed_hashLeafOut {σ : EVMState} {leaf : UInt256}
    (h : Clear.KeccakFresh.CacheInUsed σ) :
    Clear.KeccakFresh.CacheInUsed ((hashLeafOut σ leaf).2) :=
  (Clear.KeccakFresh.cacheInUsed_keccakOut (cacheInUsed_leafScratchEvm h))

lemma cacheInUsed_pushEH {σ : EVMState} {PTR : UInt256}
    (h : Clear.KeccakFresh.CacheInUsed σ) :
    Clear.KeccakFresh.CacheInUsed (pushEH σ PTR) :=
  (cacheInUsed_hashLeafOut h)

lemma cacheInUsed_guardsEvm {σ : EVMState} {V IX : UInt256}
    (h : Clear.KeccakFresh.CacheInUsed σ) :
    Clear.KeccakFresh.CacheInUsed (guardsEvm σ V IX) :=
  (cacheInUsed_leafReadEvm (Clear.KeccakFresh.cacheInUsed_accOut (Clear.KeccakFresh.cacheInUsed_accOut h)))

lemma cacheInUsed_retargetStageEvm {σ : EVMState} {LM NI V IX : UInt256}
    (h : Clear.KeccakFresh.CacheInUsed σ) :
    Clear.KeccakFresh.CacheInUsed (retargetStageEvm σ LM NI V IX) :=
  (Clear.StorageFrame.cacheInUsed_sstore (Clear.StorageFrame.cacheInUsed_sstore (Clear.StorageFrame.cacheInUsed_sstore (Clear.KeccakFresh.cacheInUsed_accOut (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ h))))))))

lemma cacheInUsed_newLeafStageEvm {σ : EVMState} {V NI4 NV5 IX1 : UInt256}
    (h : Clear.KeccakFresh.CacheInUsed σ) :
    Clear.KeccakFresh.CacheInUsed (newLeafStageEvm σ V NI4 NV5 IX1) :=
  (Clear.StorageFrame.cacheInUsed_sstore (Clear.KeccakFresh.cacheInUsed_accOut (Clear.StorageFrame.cacheInUsed_sstore (Clear.StorageFrame.cacheInUsed_sstore (Clear.StorageFrame.cacheInUsed_sstore (Clear.KeccakFresh.cacheInUsed_accOut (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ h))))))))))

lemma cacheInUsed_updTreeW (j : ℕ) {E : EVMState} {P IX : UInt256}
    (h : Clear.KeccakFresh.CacheInUsed E) :
    Clear.KeccakFresh.CacheInUsed ((updTreeW E P IX j).1) :=
  (cacheInUsed_updateWalk j (cacheInUsed_leafWriteEvm (cacheInUsed_hashLeafOut h)))

lemma cacheInUsed_insertUpdEvm (k : ℕ) {σ : EVMState} {LM NI V IX : UInt256}
    (h : Clear.KeccakFresh.CacheInUsed σ) :
    Clear.KeccakFresh.CacheInUsed (insertUpdEvm σ LM NI V IX k) :=
  (cacheInUsed_updTreeW k (cacheInUsed_retargetStageEvm h))

lemma cacheInUsed_insertNewEvm (k : ℕ) {σ : EVMState} {LM NI V IX : UInt256}
    (h : Clear.KeccakFresh.CacheInUsed σ) :
    Clear.KeccakFresh.CacheInUsed (insertNewEvm σ LM NI V IX k) :=
  (cacheInUsed_newLeafStageEvm (cacheInUsed_insertUpdEvm k h))

lemma cacheInj_leafReadEvm {σ : EVMState} {slot : UInt256}
    (hu : Clear.KeccakFresh.CacheInUsed σ) (h : Clear.KeccakFresh.CacheInj σ) :
    Clear.KeccakFresh.CacheInj (leafReadEvm σ slot) :=
  (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ h))))

lemma cacheInj_leafScratchEvm {σ : EVMState} {leaf : UInt256}
    (hu : Clear.KeccakFresh.CacheInUsed σ) (h : Clear.KeccakFresh.CacheInj σ) :
    Clear.KeccakFresh.CacheInj (leafScratchEvm σ leaf) :=
  (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ h)))))

lemma cacheInj_hashLeafOut {σ : EVMState} {leaf : UInt256}
    (hu : Clear.KeccakFresh.CacheInUsed σ) (h : Clear.KeccakFresh.CacheInj σ) :
    Clear.KeccakFresh.CacheInj ((hashLeafOut σ leaf).2) :=
  (Clear.KeccakFresh.cacheInj_keccakOut (cacheInUsed_leafScratchEvm hu) (cacheInj_leafScratchEvm hu h))

lemma cacheInj_pushEH {σ : EVMState} {PTR : UInt256}
    (hu : Clear.KeccakFresh.CacheInUsed σ) (h : Clear.KeccakFresh.CacheInj σ) :
    Clear.KeccakFresh.CacheInj (pushEH σ PTR) :=
  (cacheInj_hashLeafOut hu h)

lemma cacheInj_guardsEvm {σ : EVMState} {V IX : UInt256}
    (hu : Clear.KeccakFresh.CacheInUsed σ) (h : Clear.KeccakFresh.CacheInj σ) :
    Clear.KeccakFresh.CacheInj (guardsEvm σ V IX) :=
  (cacheInj_leafReadEvm (Clear.KeccakFresh.cacheInUsed_accOut (Clear.KeccakFresh.cacheInUsed_accOut hu)) (Clear.KeccakFresh.cacheInj_accOut (Clear.KeccakFresh.cacheInUsed_accOut hu) (Clear.KeccakFresh.cacheInj_accOut hu h)))

lemma cacheInj_retargetStageEvm {σ : EVMState} {LM NI V IX : UInt256}
    (hu : Clear.KeccakFresh.CacheInUsed σ) (h : Clear.KeccakFresh.CacheInj σ) :
    Clear.KeccakFresh.CacheInj (retargetStageEvm σ LM NI V IX) :=
  (Clear.StorageFrame.cacheInj_sstore (Clear.StorageFrame.cacheInj_sstore (Clear.StorageFrame.cacheInj_sstore (Clear.KeccakFresh.cacheInj_accOut (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ hu)))) (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ h))))))))

lemma cacheInj_newLeafStageEvm {σ : EVMState} {V NI4 NV5 IX1 : UInt256}
    (hu : Clear.KeccakFresh.CacheInUsed σ) (h : Clear.KeccakFresh.CacheInj σ) :
    Clear.KeccakFresh.CacheInj (newLeafStageEvm σ V NI4 NV5 IX1) :=
  (Clear.StorageFrame.cacheInj_sstore (Clear.KeccakFresh.cacheInj_accOut (Clear.StorageFrame.cacheInUsed_sstore (Clear.StorageFrame.cacheInUsed_sstore (Clear.StorageFrame.cacheInUsed_sstore (Clear.KeccakFresh.cacheInUsed_accOut (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ hu)))))))) (Clear.StorageFrame.cacheInj_sstore (Clear.StorageFrame.cacheInj_sstore (Clear.StorageFrame.cacheInj_sstore (Clear.KeccakFresh.cacheInj_accOut (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ hu)))) (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ h))))))))))

lemma cacheInj_updTreeW (j : ℕ) {E : EVMState} {P IX : UInt256}
    (hu : Clear.KeccakFresh.CacheInUsed E) (h : Clear.KeccakFresh.CacheInj E) :
    Clear.KeccakFresh.CacheInj ((updTreeW E P IX j).1) :=
  (cacheInj_updateWalk j (cacheInUsed_leafWriteEvm (cacheInUsed_hashLeafOut hu)) (cacheInj_leafWriteEvm (cacheInUsed_hashLeafOut hu) (cacheInj_hashLeafOut hu h)))

lemma cacheInj_insertUpdEvm (k : ℕ) {σ : EVMState} {LM NI V IX : UInt256}
    (hu : Clear.KeccakFresh.CacheInUsed σ) (h : Clear.KeccakFresh.CacheInj σ) :
    Clear.KeccakFresh.CacheInj (insertUpdEvm σ LM NI V IX k) :=
  (cacheInj_updTreeW k (cacheInUsed_retargetStageEvm hu) (cacheInj_retargetStageEvm hu h))

lemma cacheInj_insertNewEvm (k : ℕ) {σ : EVMState} {LM NI V IX : UInt256}
    (hu : Clear.KeccakFresh.CacheInUsed σ) (h : Clear.KeccakFresh.CacheInj σ) :
    Clear.KeccakFresh.CacheInj (insertNewEvm σ LM NI V IX k) :=
  (cacheInj_newLeafStageEvm (cacheInUsed_insertUpdEvm k hu) (cacheInj_insertUpdEvm k hu h))

lemma rangeInWindow_leafReadEvm {σ : EVMState} {slot : UInt256}
    (h : Clear.KeccakLowSlot.RangeInWindow σ) :
    Clear.KeccakLowSlot.RangeInWindow (leafReadEvm σ slot) :=
  (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore h))))

lemma rangeInWindow_leafScratchEvm {σ : EVMState} {leaf : UInt256}
    (h : Clear.KeccakLowSlot.RangeInWindow σ) :
    Clear.KeccakLowSlot.RangeInWindow (leafScratchEvm σ leaf) :=
  (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore h)))))

lemma rangeInWindow_hashLeafOut {σ : EVMState} {leaf : UInt256}
    (h : Clear.KeccakLowSlot.RangeInWindow σ) :
    Clear.KeccakLowSlot.RangeInWindow ((hashLeafOut σ leaf).2) :=
  (Clear.KeccakLowSlot.rangeInWindow_keccakOut (rangeInWindow_leafScratchEvm h))

lemma rangeInWindow_pushEH {σ : EVMState} {PTR : UInt256}
    (h : Clear.KeccakLowSlot.RangeInWindow σ) :
    Clear.KeccakLowSlot.RangeInWindow (pushEH σ PTR) :=
  (rangeInWindow_hashLeafOut h)

lemma rangeInWindow_guardsEvm {σ : EVMState} {V IX : UInt256}
    (h : Clear.KeccakLowSlot.RangeInWindow σ) :
    Clear.KeccakLowSlot.RangeInWindow (guardsEvm σ V IX) :=
  (rangeInWindow_leafReadEvm (rangeInWindow_accOut (rangeInWindow_accOut h)))

lemma rangeInWindow_retargetStageEvm {σ : EVMState} {LM NI V IX : UInt256}
    (h : Clear.KeccakLowSlot.RangeInWindow σ) :
    Clear.KeccakLowSlot.RangeInWindow (retargetStageEvm σ LM NI V IX) :=
  (Clear.StorageFrame.rangeInWindow_sstore (Clear.StorageFrame.rangeInWindow_sstore (Clear.StorageFrame.rangeInWindow_sstore (rangeInWindow_accOut (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore h))))))))

lemma rangeInWindow_newLeafStageEvm {σ : EVMState} {V NI4 NV5 IX1 : UInt256}
    (h : Clear.KeccakLowSlot.RangeInWindow σ) :
    Clear.KeccakLowSlot.RangeInWindow (newLeafStageEvm σ V NI4 NV5 IX1) :=
  (Clear.StorageFrame.rangeInWindow_sstore (rangeInWindow_accOut (Clear.StorageFrame.rangeInWindow_sstore (Clear.StorageFrame.rangeInWindow_sstore (Clear.StorageFrame.rangeInWindow_sstore (rangeInWindow_accOut (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore h))))))))))

lemma rangeInWindow_updTreeW (j : ℕ) {E : EVMState} {P IX : UInt256}
    (h : Clear.KeccakLowSlot.RangeInWindow E) :
    Clear.KeccakLowSlot.RangeInWindow ((updTreeW E P IX j).1) :=
  (rangeInWindow_updateWalk j (rangeInWindow_leafWriteEvm (rangeInWindow_hashLeafOut h)))

lemma rangeInWindow_insertUpdEvm (k : ℕ) {σ : EVMState} {LM NI V IX : UInt256}
    (h : Clear.KeccakLowSlot.RangeInWindow σ) :
    Clear.KeccakLowSlot.RangeInWindow (insertUpdEvm σ LM NI V IX k) :=
  (rangeInWindow_updTreeW k (rangeInWindow_retargetStageEvm h))

lemma rangeInWindow_insertNewEvm (k : ℕ) {σ : EVMState} {LM NI V IX : UInt256}
    (h : Clear.KeccakLowSlot.RangeInWindow σ) :
    Clear.KeccakLowSlot.RangeInWindow (insertNewEvm σ LM NI V IX k) :=
  (rangeInWindow_newLeafStageEvm (rangeInWindow_insertUpdEvm k h))

lemma cachedInWindow_leafReadEvm {σ : EVMState} {slot : UInt256}
    (hu : Clear.KeccakLowSlot.RangeInWindow σ) (h : Clear.KeccakLowSlot.CachedInWindow σ) :
    Clear.KeccakLowSlot.CachedInWindow (leafReadEvm σ slot) :=
  (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore h))))

lemma cachedInWindow_leafScratchEvm {σ : EVMState} {leaf : UInt256}
    (hu : Clear.KeccakLowSlot.RangeInWindow σ) (h : Clear.KeccakLowSlot.CachedInWindow σ) :
    Clear.KeccakLowSlot.CachedInWindow (leafScratchEvm σ leaf) :=
  (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore h)))))

lemma cachedInWindow_hashLeafOut {σ : EVMState} {leaf : UInt256}
    (hu : Clear.KeccakLowSlot.RangeInWindow σ) (h : Clear.KeccakLowSlot.CachedInWindow σ) :
    Clear.KeccakLowSlot.CachedInWindow ((hashLeafOut σ leaf).2) :=
  (Clear.KeccakLowSlot.cachedInWindow_keccakOut (rangeInWindow_leafScratchEvm hu) (cachedInWindow_leafScratchEvm hu h))

lemma cachedInWindow_pushEH {σ : EVMState} {PTR : UInt256}
    (hu : Clear.KeccakLowSlot.RangeInWindow σ) (h : Clear.KeccakLowSlot.CachedInWindow σ) :
    Clear.KeccakLowSlot.CachedInWindow (pushEH σ PTR) :=
  (cachedInWindow_hashLeafOut hu h)

lemma cachedInWindow_guardsEvm {σ : EVMState} {V IX : UInt256}
    (hu : Clear.KeccakLowSlot.RangeInWindow σ) (h : Clear.KeccakLowSlot.CachedInWindow σ) :
    Clear.KeccakLowSlot.CachedInWindow (guardsEvm σ V IX) :=
  (cachedInWindow_leafReadEvm (rangeInWindow_accOut (rangeInWindow_accOut hu)) (cachedInWindow_accOut (rangeInWindow_accOut hu) (cachedInWindow_accOut hu h)))

lemma cachedInWindow_retargetStageEvm {σ : EVMState} {LM NI V IX : UInt256}
    (hu : Clear.KeccakLowSlot.RangeInWindow σ) (h : Clear.KeccakLowSlot.CachedInWindow σ) :
    Clear.KeccakLowSlot.CachedInWindow (retargetStageEvm σ LM NI V IX) :=
  (Clear.StorageFrame.cachedInWindow_sstore (Clear.StorageFrame.cachedInWindow_sstore (Clear.StorageFrame.cachedInWindow_sstore (cachedInWindow_accOut (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore hu)))) (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore h))))))))

lemma cachedInWindow_newLeafStageEvm {σ : EVMState} {V NI4 NV5 IX1 : UInt256}
    (hu : Clear.KeccakLowSlot.RangeInWindow σ) (h : Clear.KeccakLowSlot.CachedInWindow σ) :
    Clear.KeccakLowSlot.CachedInWindow (newLeafStageEvm σ V NI4 NV5 IX1) :=
  (Clear.StorageFrame.cachedInWindow_sstore (cachedInWindow_accOut (Clear.StorageFrame.rangeInWindow_sstore (Clear.StorageFrame.rangeInWindow_sstore (Clear.StorageFrame.rangeInWindow_sstore (rangeInWindow_accOut (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore hu)))))))) (Clear.StorageFrame.cachedInWindow_sstore (Clear.StorageFrame.cachedInWindow_sstore (Clear.StorageFrame.cachedInWindow_sstore (cachedInWindow_accOut (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore hu)))) (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore h))))))))))

lemma cachedInWindow_updTreeW (j : ℕ) {E : EVMState} {P IX : UInt256}
    (hu : Clear.KeccakLowSlot.RangeInWindow E) (h : Clear.KeccakLowSlot.CachedInWindow E) :
    Clear.KeccakLowSlot.CachedInWindow ((updTreeW E P IX j).1) :=
  (cachedInWindow_updateWalk j (rangeInWindow_leafWriteEvm (rangeInWindow_hashLeafOut hu)) (cachedInWindow_leafWriteEvm (rangeInWindow_hashLeafOut hu) (cachedInWindow_hashLeafOut hu h)))

lemma cachedInWindow_insertUpdEvm (k : ℕ) {σ : EVMState} {LM NI V IX : UInt256}
    (hu : Clear.KeccakLowSlot.RangeInWindow σ) (h : Clear.KeccakLowSlot.CachedInWindow σ) :
    Clear.KeccakLowSlot.CachedInWindow (insertUpdEvm σ LM NI V IX k) :=
  (cachedInWindow_updTreeW k (rangeInWindow_retargetStageEvm hu) (cachedInWindow_retargetStageEvm hu h))

lemma cachedInWindow_insertNewEvm (k : ℕ) {σ : EVMState} {LM NI V IX : UInt256}
    (hu : Clear.KeccakLowSlot.RangeInWindow σ) (h : Clear.KeccakLowSlot.CachedInWindow σ) :
    Clear.KeccakLowSlot.CachedInWindow (insertNewEvm σ LM NI V IX k) :=
  (cachedInWindow_newLeafStageEvm (rangeInWindow_insertUpdEvm k hu) (cachedInWindow_insertUpdEvm k hu h))

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
