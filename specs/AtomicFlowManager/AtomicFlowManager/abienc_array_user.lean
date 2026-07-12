import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_array_bytes32_dyn_calldata

/-
  THE LEG-ARRAY ENCODER — closed form.

  `abi_encode_array_bytes32_dyn_calldata(start, length, pos)` writes the
  array length word at `pos`, guards `length < 2²⁵¹`, copies the calldata
  elements to `[pos+32, …)`, and returns the new tail
  `pos + 32·length + 32`.  The closed form keeps `calldatacopy` as the
  model's opaque state constructor; together with the outer flow encoder's
  final head writes (#44) this pins the memory layout the flowId hashes.

  (The copy FRAME — reads below `pos+32` unchanged — needs an induction
  bridge for `ByteArray.foldl`'s index loop, deferred.)

  Axiom-free.
-/

namespace generated.AtomicFlowManager.AtomicFlowManager

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

/-! ### The array-encoder closed form -/

set_option maxHeartbeats 8000000 in
/-- **Closed form of `abi_encode_array_bytes32_dyn_calldata`** (pass path,
`length < 2²⁵¹`): write the length word at `pos`, copy the element bytes to
`pos+32`, return `pos + 32·length + 32`. -/
lemma abienc_array_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {start length pos : Literal}
    {v : Identifier}
    (hlen : ¬ ((Fin.shiftLeft 1 251 - 1 : UInt256) < length)) :
    execCall (fuel+1) abi_encode_array_bytes32_dyn_calldata [v]
        (Ok evm store, [start, length, pos])
      = Ok ((evm.mstore pos length).calldatacopy (pos + 32) start
            (Fin.shiftLeft length 5))
          (store.insert v ((pos + Fin.shiftLeft length 5) + 32)) := by
  unfold execCall call abi_encode_array_bytes32_dyn_calldata
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  rw [cons, cons, cons, cons, cons, cons, cons, cons, cons, nil]
  simp only [If', LetPrimCall', AssignPrimCall', ExprStmtPrimCall', Assign',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMstore', EVMShl', EVMSub', EVMGt', EVMAdd', EVMCalldatacopy']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk ((Ok evm store)☎️⟦["start", "length", "pos"], [start, length, pos]⟧) :=
    isOk_initcall_of_isOk trivial
  obtain ⟨e0, σ0, h0⟩ := State_of_isOk hok0
  have he0 : e0 = evm := by
    have hq := congrArg State.evm h0
    rw [show (((Ok evm store)☎️⟦["start", "length", "pos"], [start, length, pos]⟧)).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at hq
    exact hq.symm
  have hst : ((Ok evm store)☎️⟦["start", "length", "pos"], [start, length, pos]⟧)["start"]!!
      = start := lookup_initcall_1
  have hle : ((Ok evm store)☎️⟦["start", "length", "pos"], [start, length, pos]⟧)["length"]!!
      = length := lookup_initcall_2 (by decide)
  have hpo : ((Ok evm store)☎️⟦["start", "length", "pos"], [start, length, pos]⟧)["pos"]!!
      = pos := lookup_initcall_3 (by decide) (by decide)
  rw [h0, he0] at hst hle hpo
  simp only [h0, he0, insert_Ok, evm_Ok]
  -- stmt 1: mstore(pos, length)
  simp only [hpo, hle]
  set E1 := evm.mstore pos length with hE1
  -- stmt 2/3: the guard constant
  simp only [setEvm_Ok, insert_Ok]
  have g1 : (Ok E1 (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 251) σ0))["split_expr_0"]!!
      = Fin.shiftLeft 1 251 := lookup_insert_self_fin
  simp only [g1]
  -- stmt 4: guard lookups and the false comparison
  have g2a : (Ok E1 (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 251 - 1)
      (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 251) σ0)))["length"]!! = length := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_ok_evm E1 evm]
    exact hle
  have g2b : (Ok E1 (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 251 - 1)
      (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 251) σ0)))["split_expr_1"]!!
      = Fin.shiftLeft 1 251 - 1 := lookup_insert_self_fin
  simp only [g2a, g2b]
  simp only [show fromBool (length > (Fin.shiftLeft 1 251 - 1 : UInt256)) = (0 : UInt256) from by
    simp only [fromBool, Bool.toUInt256, decide_eq_false hlen, if_false]]
  try simp only [List.head!]
  try rw [if_neg (by exact fun h => h rfl)]
  -- stmt 5: length_1 := shl(5, length)
  simp only [g2a]
  -- stmt 6: split_expr_2 := add(pos, 32)
  have g3 : (Ok E1 (Finmap.insert "length_1" (Fin.shiftLeft length 5)
      (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 251 - 1)
        (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 251) σ0))))["pos"]!! = pos := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_ok_evm E1 evm]
    exact hpo
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]
  simp only [g3]
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]
  -- stmt 7: the copy's three arguments
  have g4a : (Ok E1 (Finmap.insert "split_expr_2" (pos + 32)
      (Finmap.insert "length_1" (Fin.shiftLeft length 5)
        (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 251 - 1)
          (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 251) σ0)))))["split_expr_2"]!!
      = pos + 32 := lookup_insert_self_fin
  have g4b : (Ok E1 (Finmap.insert "split_expr_2" (pos + 32)
      (Finmap.insert "length_1" (Fin.shiftLeft length 5)
        (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 251 - 1)
          (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 251) σ0)))))["start"]!!
      = start := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_ok_evm E1 evm]
    exact hst
  have g4c : (Ok E1 (Finmap.insert "split_expr_2" (pos + 32)
      (Finmap.insert "length_1" (Fin.shiftLeft length 5)
        (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 251 - 1)
          (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 251) σ0)))))["length_1"]!!
      = Fin.shiftLeft length 5 := by
    rw [lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  simp only [g4a, g4b, g4c]
  set E2 := E1.calldatacopy (pos + 32) start (Fin.shiftLeft length 5) with hE2
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]
  -- stmt 8: split_expr_3 := add(pos, length_1)
  have g5a : (Ok E2 (Finmap.insert "split_expr_2" (pos + 32)
      (Finmap.insert "length_1" (Fin.shiftLeft length 5)
        (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 251 - 1)
          (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 251) σ0)))))["pos"]!! = pos := by
    rw [lookup_insert_ne_fin (by decide), lookup_ok_evm E2 E1]
    exact g3
  have g5b : (Ok E2 (Finmap.insert "split_expr_2" (pos + 32)
      (Finmap.insert "length_1" (Fin.shiftLeft length 5)
        (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 251 - 1)
          (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 251) σ0)))))["length_1"]!!
      = Fin.shiftLeft length 5 := by
    rw [lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  simp only [g5a, g5b]
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]
  -- stmt 9: ret := add(split_expr_3, 32)
  have g6 : (Ok E2 (Finmap.insert "split_expr_3" (pos + Fin.shiftLeft length 5)
      (Finmap.insert "split_expr_2" (pos + 32)
        (Finmap.insert "length_1" (Fin.shiftLeft length 5)
          (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 251 - 1)
            (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 251) σ0))))))["split_expr_3"]!!
      = pos + Fin.shiftLeft length 5 := lookup_insert_self_fin
  simp only [g6]
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]
  -- rets lookup
  have g7 : (Ok E2 (Finmap.insert "end_clear_sanitised_hrafn"
      ((pos + Fin.shiftLeft length 5) + 32)
      (Finmap.insert "split_expr_3" (pos + Fin.shiftLeft length 5)
        (Finmap.insert "split_expr_2" (pos + 32)
          (Finmap.insert "length_1" (Fin.shiftLeft length 5)
            (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 251 - 1)
              (Finmap.insert "split_expr_0" (Fin.shiftLeft 1 251) σ0)))))))["end_clear_sanitised_hrafn"]!!
      = (pos + Fin.shiftLeft length 5) + 32 := lookup_insert_self_fin
  try simp only [g7]
  try rw [reviveJump_of_isOk (by trivial)]
  try simp only [overwrite?_of_Ok]
  try rw [setStore_ok]
  try simp only [multifill_cons, multifill_nil, insert_Ok]
  try rw [hE2, hE1]

end

end generated.AtomicFlowManager.AtomicFlowManager
