import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.L2InteropHandler.L2InteropHandler.mem_helpers_user
import specs.CalldatacopyFrame
import generated.L2InteropHandler.L2InteropHandler.fun_formatEvmV1

/-
  `fun_formatEvmV1` ARC (L2InteropHandler) — the interop-address encoder.

  The function starts with a five-stage binary magnitude probe of the chain
  id (byte-length computation).  This file drives the SMALL-CHAIN-ID class
  (`chainid < 2^8`, i.e. every probe shift is zero): all five branch ifs are
  skipped, `var_value` stays the chain id, and `var_result` stays `0`.  The
  formatting tail composes on top of this arm (`slice_call` etc.).

  Axiom-free.
-/

namespace generated.L2InteropHandler.L2InteropHandler

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

private lemma lookup_ok_evm {σ : VarStore} {k : Identifier} (e e' : EVMState) :
    (Ok e σ)[k]!! = (Ok e' σ)[k]!! := rfl

private lemma reviveJump_of_isOk {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok]; exact lookup_insert_of_ne h

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

/-! ### The magnitude probe prefix, quoted verbatim -/

/-- The five-stage magnitude probe of `fun_formatEvmV1` (statements 1–16 of
the generated body). -/
@[reducible] private def magnitudeProbe : Stmt := <s
  {
    let var_value := var_chainid
    let var_result := 0
    let result := shr(128, var_chainid)
    let split_expr_0 := iszero(result)
    if iszero(split_expr_0)
    {
        var_value := result
        var_result := 16
    }
    let result_1 := shr(64, var_value)
    let split_expr_1 := iszero(result_1)
    if iszero(split_expr_1)
    {
        var_value := result_1
        var_result := add(var_result, 8)
    }
    let result_2 := shr(32, var_value)
    let split_expr_2 := iszero(result_2)
    if iszero(split_expr_2)
    {
        var_value := result_2
        var_result := add(var_result, 4)
    }
    let result_3 := shr(16, var_value)
    let split_expr_3 := iszero(result_3)
    if iszero(split_expr_3)
    {
        var_value := result_3
        var_result := add(var_result, 2)
    }
    let split_expr_4 := shr(8, var_value)
    let split_expr_5 := iszero(split_expr_4)
}
>

/-- **Small-chain-id magnitude probe**: when every probe shift of the chain id
is zero (`chainid < 2^8`), all five branch ifs are skipped — `var_value` stays
the chain id and `var_result` stays `0`. -/
private lemma magnitude_probe_small
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {C : Literal}
    (hc : (Ok evm σ)["var_chainid"]!! = C)
    (h128 : Fin.shiftRight C 128 = 0)
    (h64 : Fin.shiftRight C 64 = 0)
    (h32 : Fin.shiftRight C 32 = 0)
    (h16 : Fin.shiftRight C 16 = 0)
    (h8 : Fin.shiftRight C 8 = 0) :
    exec (fuel+1) magnitudeProbe (Ok evm σ)
      = Ok evm (((((((((((( σ.insert "var_value" C).insert
          "var_result" 0).insert "result" 0).insert "split_expr_0" 1).insert
          "result_1" 0).insert "split_expr_1" 1).insert
          "result_2" 0).insert "split_expr_2" 1).insert
          "result_3" 0).insert "split_expr_3" 1).insert
          "split_expr_4" 0).insert "split_expr_5" 1) := by
  unfold magnitudeProbe
  -- let var_value := var_chainid
  rw [cons, LetEq']
  simp only [Var', insert_Ok]
  rw [hc]
  -- let var_result := 0
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  -- let result := shr(128, var_chainid)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShr',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hc]
  rw [h128]
  -- let split_expr_0 := iszero(result)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMIszero',
             insert_Ok]
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  -- if iszero(split_expr_0) — skip
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- let result_1 := shr(64, var_value)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShr',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [h64]
  -- let split_expr_1 := iszero(result_1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMIszero',
             insert_Ok]
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  -- if iszero(split_expr_1) — skip
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- let result_2 := shr(32, var_value)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShr',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [h32]
  -- let split_expr_2 := iszero(result_2)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMIszero',
             insert_Ok]
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  -- if iszero(split_expr_2) — skip
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- let result_3 := shr(16, var_value)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShr',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [h16]
  -- let split_expr_3 := iszero(result_3)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMIszero',
             insert_Ok]
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  -- if iszero(split_expr_3) — skip
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- let split_expr_4 := shr(8, var_value)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShr',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [h8]
  -- let split_expr_5 := iszero(split_expr_4)
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMIszero',
             insert_Ok]
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]

/-! ### The small-case allocation chunk -/

/-- The allocation chunk that runs when the byte-length probe concluded a
single byte would NOT suffice for the padded format — for the small-chain-id
class this is the 32-byte staging write: put the chain id at `F + 32`, the
length `32` at `F`, and bump the free pointer by 64. -/
@[reducible] private def formatAllocChunk : Stmt := <s
  {
      let expr_mpos := mload(64)
      let split_expr_6 := add(expr_mpos, 32)
      mstore(split_expr_6, var_chainid)
      mstore(expr_mpos, 32)
      finalize_allocation(expr_mpos, 64)
  }
>

/-- **Allocation chunk closed form** (`F := mload 64`): stage the chain id and
the length word, bump the free pointer to `F + 64`. -/
private lemma format_allocA_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {C : Literal}
    (hC : (Ok evm σ)["var_chainid"]!! = C)
    (hf1 : ¬ (evm.mload 64 + 64 > (18446744073709551615 : UInt256)))
    (hf2 : ¬ (evm.mload 64 + 64 < evm.mload 64)) :
    exec (fuel+1) formatAllocChunk (Ok evm σ)
      = Ok (((evm.mstore (evm.mload 64 + 32) C).mstore (evm.mload 64) 32).mstore
            64 (evm.mload 64 + 64))
          ((σ.insert "expr_mpos" (evm.mload 64)).insert
            "split_expr_6" (evm.mload 64 + 32)) := by
  unfold formatAllocChunk
  -- let expr_mpos := mload(64)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMload',
             evm_Ok, insert_Ok]
  -- let split_expr_6 := add(expr_mpos, 32)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_self_fin]
  -- mstore(split_expr_6, var_chainid)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hC]
  -- mstore(expr_mpos, 32)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  -- finalize_allocation(expr_mpos, 64)
  rw [cons, nil, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [finalize_alloc_call
    (by rw [show Fin.land ((64 : UInt256) + 31) (Clear.UInt256.lnot 31)
          = (64 : UInt256) from by decide]
        exact hf1)
    (by rw [show Fin.land ((64 : UInt256) + 31) (Clear.UInt256.lnot 31)
          = (64 : UInt256) from by decide]
        exact hf2)]
  rw [show Fin.land ((64 : UInt256) + 31) (Clear.UInt256.lnot 31)
    = (64 : UInt256) from by decide]

/-! ### The slice chunk (small case) -/

/-- The slice chunk: recover the payload window `[31, 32)` of the staged
32-byte word — the single low byte of the chain id. -/
@[reducible] private def formatSliceChunk : Stmt := <s
  {
      let split_expr_7 := sub(32, var_result)
      let split_expr_8 := not(0)
      let split_expr_9 := add(split_expr_7, split_expr_8)
      let split_expr_10 := mload(expr_mpos)
      let var_mpos := fun_slice(expr_mpos, split_expr_9, split_expr_10)
  }
>

/-- **Slice chunk closed form (small case)**: with `var_result = 0` and the
staged length word read back as `32`, the chunk slices `[31, 32)` — a fresh
1-byte array at the current free pointer. -/
private lemma format_sliceB_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {F : Literal}
    (hres : (Ok evm σ)["var_result"]!! = 0)
    (hmp : (Ok evm σ)["expr_mpos"]!! = F)
    (hlen32 : evm.mload F = 32)
    (hp1 : ¬ (evm.mload 64 + 64 > (18446744073709551615 : UInt256)))
    (hp2 : ¬ (evm.mload 64 + 64 < evm.mload 64)) :
    exec (fuel+1) formatSliceChunk (Ok evm σ)
      = Ok ((sliceEvmA evm F 31).calldatacopy (evm.mload 64 + 32)
            (((sliceEvmA evm F 31).execution_env.input_data.size : UInt256))
            (Fin.land (evm.mload F - 31 + 31) (Clear.UInt256.lnot 31) + 32
              + Clear.UInt256.lnot 31))
          (((((σ.insert "split_expr_7" 32).insert
            "split_expr_8" (Clear.UInt256.lnot 0)).insert
            "split_expr_9" 31).insert "split_expr_10" 32).insert
            "var_mpos" (evm.mload 64)) := by
  unfold formatSliceChunk
  -- let split_expr_7 := sub(32, var_result)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMSub',
             insert_Ok]
  rw [hres]
  rw [show (32 : UInt256) - 0 = (32 : UInt256) from by decide]
  -- let split_expr_8 := not(0)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMNot',
             insert_Ok]
  -- let split_expr_9 := add(split_expr_7, split_expr_8)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_self_fin, lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [show (32 : UInt256) + Clear.UInt256.lnot 0 = (31 : UInt256) from by decide]
  -- let split_expr_10 := mload(expr_mpos)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMload',
             evm_Ok, insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), hmp]
  rw [hlen32]
  -- let var_mpos := fun_slice(expr_mpos, split_expr_9, split_expr_10)
  rw [cons, nil, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [show (Ok evm (Finmap.insert "split_expr_10" 32
        (Finmap.insert "split_expr_9" 31
          (Finmap.insert "split_expr_8" (Clear.UInt256.lnot 0)
            (Finmap.insert "split_expr_7" 32 σ)))))["split_expr_9"]!!
      = (31 : UInt256) from by
    rw [lookup_insert_ne_fin (by decide)]; exact lookup_insert_self_fin]
  rw [lookup_insert_self_fin]
  rw [show (Ok evm (Finmap.insert "split_expr_10" 32
        (Finmap.insert "split_expr_9" 31
          (Finmap.insert "split_expr_8" (Clear.UInt256.lnot 0)
            (Finmap.insert "split_expr_7" 32 σ)))))["expr_mpos"]!!
      = F from by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact hmp]
  rw [slice_call
    (by rw [hlen32]; decide)
    (by rw [hlen32]; decide)
    (by rw [hlen32]; decide)
    (by rw [hlen32]; decide)
    (by rw [hlen32]
        rw [show Fin.land ((Fin.land ((32 : UInt256) - 31 + 31)
            (Clear.UInt256.lnot 31) + 32) + 31) (Clear.UInt256.lnot 31)
          = (64 : UInt256) from by decide]
        exact hp1)
    (by rw [hlen32]
        rw [show Fin.land ((Fin.land ((32 : UInt256) - 31 + 31)
            (Clear.UInt256.lnot 31) + 32) + 31) (Clear.UInt256.lnot 31)
          = (64 : UInt256) from by decide]
        exact hp2)]
  rw [hlen32]

/-! ### The tag-prefix chunks -/

/-- Chunk D: read the sliced byte word, take the new free pointer, write the
`0x0001` version tag at `P₂ + 32`. -/
@[reducible] private def formatTagChunk : Stmt := <s
  {
      let _1 := mload(var_mpos)
      let expr_mpos_1 := mload(64)
      let split_expr_11 := add(expr_mpos_1, 32)
      let split_expr_12 := shl(240, 1)
      mstore(split_expr_11, split_expr_12)
  }
>

/-- Chunk E: write the chain-id byte (masked to the top byte) at `P₂ + 36`. -/
@[reducible] private def formatByteChunk : Stmt := <s
  {
      let split_expr_13 := add(expr_mpos_1, 36)
      let split_expr_14 := shl(248, _1)
      let split_expr_15 := shl(248, 255)
      let split_expr_16 := and(split_expr_14, split_expr_15)
      mstore(split_expr_13, split_expr_16)
  }
>

/-- **Chunk D closed form**: with the slice pointer's word read back as `B₁`
(hypothesis), stage the version tag. -/
private lemma format_tagD_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {VP B1 : Literal}
    (hvm : (Ok evm σ)["var_mpos"]!! = VP)
    (h1r : evm.mload VP = B1) :
    exec (fuel+1) formatTagChunk (Ok evm σ)
      = Ok (evm.mstore (evm.mload 64 + 32) (Fin.shiftLeft 1 240))
          ((((σ.insert "_1" B1).insert
            "expr_mpos_1" (evm.mload 64)).insert
            "split_expr_11" (evm.mload 64 + 32)).insert
            "split_expr_12" (Fin.shiftLeft 1 240)) := by
  unfold formatTagChunk
  -- let _1 := mload(var_mpos)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMload',
             evm_Ok, insert_Ok]
  rw [hvm, h1r]
  -- let expr_mpos_1 := mload(64)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMload',
             evm_Ok, insert_Ok]
  -- let split_expr_11 := add(expr_mpos_1, 32)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_self_fin]
  -- let split_expr_12 := shl(240, 1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- mstore(split_expr_11, split_expr_12)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin,
      lookup_insert_ne_fin (by decide), lookup_insert_self_fin]

/-- **Chunk E closed form**: mask the sliced byte to the top position and
write it after the tag. -/
private lemma format_byteE_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {P2 B1 : Literal}
    (hemp : (Ok evm σ)["expr_mpos_1"]!! = P2)
    (h1v : (Ok evm σ)["_1"]!! = B1) :
    exec (fuel+1) formatByteChunk (Ok evm σ)
      = Ok (evm.mstore (P2 + 36)
            (Fin.land (Fin.shiftLeft B1 248) (Fin.shiftLeft 255 248)))
          ((((σ.insert "split_expr_13" (P2 + 36)).insert
            "split_expr_14" (Fin.shiftLeft B1 248)).insert
            "split_expr_15" (Fin.shiftLeft 255 248)).insert
            "split_expr_16" (Fin.land (Fin.shiftLeft B1 248) (Fin.shiftLeft 255 248))) := by
  unfold formatByteChunk
  -- let split_expr_13 := add(expr_mpos_1, 36)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [hemp]
  -- let split_expr_14 := shl(248, _1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), h1v]
  -- let split_expr_15 := shl(248, 255)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- let split_expr_16 := and(split_expr_14, split_expr_15)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAnd',
             insert_Ok]
  rw [lookup_insert_self_fin,
      lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  -- mstore(split_expr_13, split_expr_16)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin,
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_self_fin]

/-! ### The payload and address-locator chunks -/

/-- Chunk F: copy the sliced payload behind the tag (A3 no-op) and set the
running end pointer. -/
@[reducible] private def formatCopyChunk : Stmt := <s
  {
      let length := mload(var_mpos)
      let split_expr_17 := add(expr_mpos_1, 37)
      let split_expr_18 := add(var_mpos, 32)
      mcopy(split_expr_17, split_expr_18, length)
      let _2 := add(expr_mpos_1, length)
  }
>

/-- Chunk G: write the `0x05` address-length tag and shift the address up. -/
@[reducible] private def formatAddrTagChunk : Stmt := <s
  {
      let split_expr_19 := add(_2, 37)
      let split_expr_20 := shl(250, 5)
      mstore(split_expr_19, split_expr_20)
      let split_expr_21 := add(_2, 38)
      let split_expr_22 := shl(96, var_addr)
  }
>

/-- **Chunk F closed form**: with the slice length read back as `LN`
(hypothesis), the payload `mcopy` is the A3 no-op and only the store grows. -/
private lemma format_copyF_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {VP P2 LN : Literal}
    (hvm : (Ok evm σ)["var_mpos"]!! = VP)
    (hemp : (Ok evm σ)["expr_mpos_1"]!! = P2)
    (hlr : evm.mload VP = LN) :
    exec (fuel+1) formatCopyChunk (Ok evm σ)
      = Ok evm ((((σ.insert "length" LN).insert
          "split_expr_17" (P2 + 37)).insert
          "split_expr_18" (VP + 32)).insert
          "_2" (P2 + LN)) := by
  unfold formatCopyChunk
  -- let length := mload(var_mpos)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMload',
             evm_Ok, insert_Ok]
  rw [hvm, hlr]
  -- let split_expr_17 := add(expr_mpos_1, 37)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), hemp]
  -- let split_expr_18 := add(var_mpos, 32)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hvm]
  -- mcopy(split_expr_17, split_expr_18, length)
  rw [cons, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [mcopy_call]
  -- let _2 := add(expr_mpos_1, length)
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [show (Ok evm (Finmap.insert "split_expr_18" (VP + 32)
        (Finmap.insert "split_expr_17" (P2 + 37)
          (Finmap.insert "length" LN σ))))["length"]!! = LN from by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin]
  rw [show (Ok evm (Finmap.insert "split_expr_18" (VP + 32)
        (Finmap.insert "split_expr_17" (P2 + 37)
          (Finmap.insert "length" LN σ))))["expr_mpos_1"]!! = P2 from by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide)]
    exact hemp]

/-- **Chunk G closed form**: locator tag write and address shift. -/
private lemma format_addrG_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {T2 A : Literal}
    (h2 : (Ok evm σ)["_2"]!! = T2)
    (ha : (Ok evm σ)["var_addr"]!! = A) :
    exec (fuel+1) formatAddrTagChunk (Ok evm σ)
      = Ok (evm.mstore (T2 + 37) (Fin.shiftLeft 5 250))
          ((((σ.insert "split_expr_19" (T2 + 37)).insert
            "split_expr_20" (Fin.shiftLeft 5 250)).insert
            "split_expr_21" (T2 + 38)).insert
            "split_expr_22" (Fin.shiftLeft A 96)) := by
  unfold formatAddrTagChunk
  -- let split_expr_19 := add(_2, 37)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [h2]
  -- let split_expr_20 := shl(250, 5)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- mstore(split_expr_19, split_expr_20)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin,
      lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  -- let split_expr_21 := add(_2, 38)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_ok_evm _ evm, h2]
  -- let split_expr_22 := shl(96, var_addr)
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_ok_evm _ evm, ha]

/-! ### The address-write and length-fix chunks -/

/-- Chunk H: mask the shifted address and write it; compute the format
length. -/
@[reducible] private def formatAddrWriteChunk : Stmt := <s
  {
      let split_expr_23 := not(79228162514264337593543950335)
      let split_expr_24 := and(split_expr_22, split_expr_23)
      mstore(split_expr_21, split_expr_24)
      let split_expr_25 := sub(_2, expr_mpos_1)
      let _3 := add(split_expr_25, 37)
  }
>

/-- Chunk I: fix the byte-array length word and finalize the allocation. -/
@[reducible] private def formatFinalChunk : Stmt := <s
  {
      let split_expr_26 := not(10)
      let split_expr_27 := add(_3, split_expr_26)
      mstore(expr_mpos_1, split_expr_27)
      let split_expr_28 := add(_3, 21)
      finalize_allocation(expr_mpos_1, split_expr_28)
  }
>

/-- **Chunk H closed form**: masked address write and length computation. -/
private lemma format_addrH_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {SA W T2 P2 : Literal}
    (h22 : (Ok evm σ)["split_expr_22"]!! = SA)
    (h21 : (Ok evm σ)["split_expr_21"]!! = W)
    (h2v : (Ok evm σ)["_2"]!! = T2)
    (hemp : (Ok evm σ)["expr_mpos_1"]!! = P2) :
    exec (fuel+1) formatAddrWriteChunk (Ok evm σ)
      = Ok (evm.mstore W
            (Fin.land SA (Clear.UInt256.lnot 79228162514264337593543950335)))
          ((((σ.insert "split_expr_23"
            (Clear.UInt256.lnot 79228162514264337593543950335)).insert
            "split_expr_24"
            (Fin.land SA (Clear.UInt256.lnot 79228162514264337593543950335))).insert
            "split_expr_25" (T2 - P2)).insert
            "_3" (T2 - P2 + 37)) := by
  unfold formatAddrWriteChunk
  -- let split_expr_23 := not(...)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMNot',
             insert_Ok]
  -- let split_expr_24 := and(split_expr_22, split_expr_23)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAnd',
             insert_Ok]
  rw [lookup_insert_self_fin, lookup_insert_ne_fin (by decide), h22]
  -- mstore(split_expr_21, split_expr_24)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), h21]
  -- let split_expr_25 := sub(_2, expr_mpos_1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMSub',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_ok_evm _ evm, h2v]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_ok_evm _ evm, hemp]
  -- let _3 := add(split_expr_25, 37)
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_self_fin]

/-- **Chunk I closed form**: the length-word fix-up (`_3 - 11`) and the final
allocation bump. -/
private lemma format_finalI_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {L3 P2 : Literal}
    (h3 : (Ok evm σ)["_3"]!! = L3)
    (hemp : (Ok evm σ)["expr_mpos_1"]!! = P2)
    (hf1 : ¬ (P2 + Fin.land ((L3 + 21) + 31) (Clear.UInt256.lnot 31)
      > (18446744073709551615 : UInt256)))
    (hf2 : ¬ (P2 + Fin.land ((L3 + 21) + 31) (Clear.UInt256.lnot 31) < P2)) :
    exec (fuel+1) formatFinalChunk (Ok evm σ)
      = Ok ((evm.mstore P2 (L3 + Clear.UInt256.lnot 10)).mstore 64
            (P2 + Fin.land ((L3 + 21) + 31) (Clear.UInt256.lnot 31)))
          (((σ.insert "split_expr_26" (Clear.UInt256.lnot 10)).insert
            "split_expr_27" (L3 + Clear.UInt256.lnot 10)).insert
            "split_expr_28" (L3 + 21)) := by
  unfold formatFinalChunk
  -- let split_expr_26 := not(10)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMNot',
             insert_Ok]
  -- let split_expr_27 := add(_3, split_expr_26)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_self_fin, lookup_insert_ne_fin (by decide), h3]
  -- mstore(expr_mpos_1, split_expr_27)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hemp]
  -- let split_expr_28 := add(_3, 21)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_ok_evm _ evm, h3]
  -- finalize_allocation(expr_mpos_1, split_expr_28)
  rw [cons, nil, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_ok_evm _ evm, hemp]
  rw [finalize_alloc_call hf1 hf2]

/-! ### Assembly recipe (for the closing session)

`formatEvmV1_small_call` — the full `execCall` closed form of
`fun_formatEvmV1` on the small-chain-id class — is pure transcription from
here.  Everything needed is proven; this block records the exact plan.

**EVM stages** (define as `@[reducible]` abbreviations; `F := evm.mload 64`):
- `E1 := ((evm.mstore (F+32) C).mstore F 32).mstore 64 (F+64)`   (chunk A)
- `E2 := (sliceEvmA E1 F 31).calldatacopy (E1.mload 64 + 32) (…input_data.size) (…)`  (chunk B; `VP := E1.mload 64`)
- `E3 := E2.mstore (E2.mload 64 + 32) (Fin.shiftLeft 1 240)`      (chunk D; `P2 := E2.mload 64`)
- `E4 := E3.mstore (P2+36) (Fin.land (Fin.shiftLeft B1 248) (Fin.shiftLeft 255 248))` (chunk E)
- `E5 := E4.mstore (T2+37) (Fin.shiftLeft 5 250)`                 (chunk G; `T2 := P2 + LN`)
- `E6 := E5.mstore (T2+38) (Fin.land (Fin.shiftLeft A 96) (Clear.UInt256.lnot 79228162514264337593543950335))` (chunk H)
- `E7 := (E6.mstore P2 (L3 + Clear.UInt256.lnot 10)).mstore 64 (P2 + Fin.land ((L3+21)+31) (Clear.UInt256.lnot 31))` (chunk I; `L3 := T2 - P2 + 37`)

**Hypotheses**: `h128 h64 h32 h16 h8` (probe shifts of `C` zero);
`hf1a hf2a` (`format_allocA_arm`'s finalize bounds at `(F, 64)`);
`hlen32 : E1.mload F = 32` — dischargeable: `mload_mstore_self_at` at `F`
through `mload_mstore_outside` for the 64-write (needs `96 ≤ F.val`,
`F.val + 32 ≤ 2^256`); `hp1 hp2` (sliceB bounds at `E1`);
`h1r : E2.mload VP = B1` — `mload_calldatacopy_below` (read `VP` below the
copy at `VP+32`) then `mload_mstore_self_at` inside `sliceEvmA` (value `1`);
`hlr : E4.mload VP = LN` — same chain plus `mload_mstore_outside` for the
D/E writes (disjointness `P2 ≥ VP + 64`-class); `hfI1 hfI2` (chunk I bounds).

**Drive order**: initcall boilerplate (params `var_chainid, var_addr` →
`C, A`; `set J`; destructure with the have-rewrite, NOT subst) → probe-16
inline (iteration-30 template with `hcJ` transports; tower depth 12) →
skip-if `iszero(split_expr_5)` (try-chain) → `format_allocA_arm` (hC peel 12
+ transport) → `format_sliceB_arm` (hres peel 10-to-var_result; hmp peel 1;
hlen32) → `format_tagD_arm` (hvm peel 4-to-var_mpos; h1r) →
`format_byteE_arm` (hemp peel 3; h1v peel 3) → `format_copyF_arm` (hvm/hemp
deep peels; hlr) → `format_addrG_arm` (h2 peel 0-top; ha peel ~20 +
transport `lookup_initcall_2`) → `format_addrH_arm` (h22 top; h21 peel 1;
h2v/hemp deep) → `format_finalI_arm` (h3 top; hemp deep) → ret chunk
(`rw [cons,nil]; rw [cons,nil,Assign']` + `expr_mpos_1` deep peel) → ret
lookup + wrapper collapse (State_of_isOk + reviveJump/overwrite?/setStore).
Read exact towers from goals (`trace_state` where `rfl` recurses); expect
`lookup_ok_evm` hops at every evm-crossing transport.

**Computed peel counts** (ne-peels before the closing self/transport):
probe var_chainid 2 (then hcJ); var_value reads 3/5/7/9; allocA hC 12+hop;
sliceB hres 12, hmp 1; tagD hvm 0; byteE hemp 2, h1v 3; copyF hvm 8, hemp 6;
addrG h2 0, ha 31+hop→initcall_2; addrH h22 0, h21 1, h2v 4, hemp 14;
finalI h3 0, hemp 18; ret expr_mpos_1 21; ret-multifill self. -/

/-! ### Readback dischargers -/

/-- **The staged length word reads back** (`hlen32`'s discharger): after the
allocation chunk's three writes, reading the word at the old free pointer `F`
returns the staged `32`: the 64-write is disjoint (`96 ≤ F`), and the `F`
write — the outermost remaining — round-trips.  The `F+32` write is shadowed
and never consulted. -/
lemma alloc_len_readback
    {evm : EVMState} {C : Literal}
    (h96 : 96 ≤ (evm.mload 64).val)
    (hF32 : (evm.mload 64).val + 32 ≤ 2 ^ 256) :
    (((evm.mstore (evm.mload 64 + 32) C).mstore (evm.mload 64) 32).mstore 64
        (evm.mload 64 + 64)).mload (evm.mload 64) = 32 := by
  have h64v : ((64 : UInt256)).val = 64 := by decide
  rw [mload_mstore_outside _ 64 _ _ (by rw [h64v]; norm_num) hF32
      (Or.inr (by rw [h64v]; exact h96))]
  exact mload_mstore_self_at _ _ 32 hF32

/-- **The slice array's length word reads back** (`h1r`/`hlr`'s core): reading
the slice pointer `VP = E1.mload 64` through the post-slice state — the scratch
copy lands strictly above (`VP + 32`), and `sliceEvmA`'s outermost write is at
`VP` itself — returns the slice length `E1.mload F - 31` (with the staged
readback, `32 - 31 = 1`). -/
lemma slice_len_readback
    {E1 : EVMState} {F CDS SZ2 : UInt256}
    (hVP32 : (E1.mload 64).val + 32 ≤ 2 ^ 256)
    (hcp : (E1.mload 64).val + 32 ≤ (E1.mload 64 + 32).val)
    (hnw : (E1.mload 64 + 32).val
        + (ByteArray.extractBytes CDS.val SZ2.val
            (sliceEvmA E1 F 31).execution_env.input_data).size
        + 31 ≤ 2 ^ 256) :
    ((sliceEvmA E1 F 31).calldatacopy (E1.mload 64 + 32) CDS SZ2).mload
        (E1.mload 64)
      = E1.mload F - 31 := by
  rw [Clear.CalldatacopyFrame.mload_calldatacopy_below hcp hnw]
  exact mload_mstore_self_at _ _ _ hVP32

/-! ### The assembly -/

/-- Stage abbreviations of the small-chain-id closed form. -/
@[reducible] def fmtE1 (evm : EVMState) (C : Literal) : EVMState :=
  ((evm.mstore (evm.mload 64 + 32) C).mstore (evm.mload 64) 32).mstore 64
    (evm.mload 64 + 64)

@[reducible] def fmtE2 (evm : EVMState) (C : Literal) : EVMState :=
  (sliceEvmA (fmtE1 evm C) (evm.mload 64) 31).calldatacopy
    ((fmtE1 evm C).mload 64 + 32)
    (((sliceEvmA (fmtE1 evm C) (evm.mload 64) 31).execution_env.input_data.size : UInt256))
    (Fin.land ((fmtE1 evm C).mload (evm.mload 64) - 31 + 31) (Clear.UInt256.lnot 31) + 32
      + Clear.UInt256.lnot 31)

@[reducible] def fmtE3 (evm : EVMState) (C : Literal) : EVMState :=
  (fmtE2 evm C).mstore ((fmtE2 evm C).mload 64 + 32) (Fin.shiftLeft 1 240)

@[reducible] def fmtE4 (evm : EVMState) (C B1 : Literal) : EVMState :=
  (fmtE3 evm C).mstore ((fmtE2 evm C).mload 64 + 36)
    (Fin.land (Fin.shiftLeft B1 248) (Fin.shiftLeft 255 248))

@[reducible] def fmtE5 (evm : EVMState) (C B1 LN : Literal) : EVMState :=
  (fmtE4 evm C B1).mstore (((fmtE2 evm C).mload 64 + LN) + 37) (Fin.shiftLeft 5 250)

@[reducible] def fmtE6 (evm : EVMState) (C B1 LN A : Literal) : EVMState :=
  (fmtE5 evm C B1 LN).mstore (((fmtE2 evm C).mload 64 + LN) + 38)
    (Fin.land (Fin.shiftLeft A 96)
      (Clear.UInt256.lnot 79228162514264337593543950335))

@[reducible] def fmtL3 (evm : EVMState) (C LN : Literal) : Literal :=
  ((fmtE2 evm C).mload 64 + LN) - (fmtE2 evm C).mload 64 + 37

@[reducible] def fmtE7 (evm : EVMState) (C B1 LN A : Literal) : EVMState :=
  ((fmtE6 evm C B1 LN A).mstore ((fmtE2 evm C).mload 64)
    (fmtL3 evm C LN + Clear.UInt256.lnot 10)).mstore 64
    ((fmtE2 evm C).mload 64
      + Fin.land ((fmtL3 evm C LN + 21) + 31) (Clear.UInt256.lnot 31))

/-- **`fun_formatEvmV1`, small-chain-id closed form** (readbacks
hypothesis-style — `alloc_len_readback` / `slice_len_readback` +
`mload_mstore_outside₂` discharge them). -/
lemma formatEvmV1_small_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    {C A B1 LN : Literal} {t : Identifier}
    (h128 : Fin.shiftRight C 128 = 0) (h64 : Fin.shiftRight C 64 = 0)
    (h32 : Fin.shiftRight C 32 = 0) (h16 : Fin.shiftRight C 16 = 0)
    (h8 : Fin.shiftRight C 8 = 0)
    (hf1a : ¬ (evm.mload 64 + 64 > (18446744073709551615 : UInt256)))
    (hf2a : ¬ (evm.mload 64 + 64 < evm.mload 64))
    (hlen32 : (fmtE1 evm C).mload (evm.mload 64) = 32)
    (hp1 : ¬ ((fmtE1 evm C).mload 64 + 64 > (18446744073709551615 : UInt256)))
    (hp2 : ¬ ((fmtE1 evm C).mload 64 + 64 < (fmtE1 evm C).mload 64))
    (h1r : (fmtE2 evm C).mload ((fmtE1 evm C).mload 64) = B1)
    (hlr : (fmtE4 evm C B1).mload ((fmtE1 evm C).mload 64) = LN)
    (hfI1 : ¬ ((fmtE2 evm C).mload 64
      + Fin.land ((fmtL3 evm C LN + 21) + 31) (Clear.UInt256.lnot 31)
      > (18446744073709551615 : UInt256)))
    (hfI2 : ¬ ((fmtE2 evm C).mload 64
      + Fin.land ((fmtL3 evm C LN + 21) + 31) (Clear.UInt256.lnot 31)
      < (fmtE2 evm C).mload 64)) :
    execCall (fuel+1) fun_formatEvmV1 [t] (Ok evm store, [C, A])
      = Ok (fmtE7 evm C B1 LN A)
          (store.insert t ((fmtE2 evm C).mload 64)) := by
  unfold execCall call fun_formatEvmV1
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  have hok0 : isOk ((Ok evm store)☎️⟦["var_chainid", "var_addr"], [C, A]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["var_chainid", "var_addr"], [C, A]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  set J := (Ok evm store)☎️⟦["var_chainid", "var_addr"], [C, A]⟧
  obtain ⟨e0, σ0, hJ0⟩ := State_of_isOk hok0
  have he0 : e0 = evm := by
    have h := congrArg State.evm hJ0
    rw [hevm0] at h
    exact h.symm
  have hJ0' : J = Ok evm σ0 := by rw [hJ0, he0]
  rw [hJ0']
  have hcJ : (Ok evm σ0)["var_chainid"]!! = C := by
    rw [← hJ0']; exact lookup_initcall_1
  -- let var_value := var_chainid
  rw [cons, LetEq']
  simp only [Var', insert_Ok]
  rw [hcJ]
  -- let var_result := 0
  rw [cons, LetEq']
  simp only [Lit', insert_Ok]
  -- let result := shr(128, var_chainid)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShr',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hcJ]
  rw [h128]
  -- let split_expr_0 := iszero(result)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMIszero',
             insert_Ok]
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  -- if iszero(split_expr_0) — skip
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- let result_1 := shr(64, var_value)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShr',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [h64]
  -- let split_expr_1 := iszero(result_1)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMIszero',
             insert_Ok]
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  -- if iszero(split_expr_1) — skip
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- let result_2 := shr(32, var_value)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShr',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [h32]
  -- let split_expr_2 := iszero(result_2)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMIszero',
             insert_Ok]
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  -- if iszero(split_expr_2) — skip
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- let result_3 := shr(16, var_value)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShr',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [h16]
  -- let split_expr_3 := iszero(result_3)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMIszero',
             insert_Ok]
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  -- if iszero(split_expr_3) — skip
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- let split_expr_4 := shr(8, var_value)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShr',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [h8]
  -- let split_expr_5 := iszero(split_expr_4)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMIszero',
             insert_Ok]
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  try simp only [show decide ((0 : UInt256) = 0) = true from by decide]
  try simp only [show fromBool true = (1 : UInt256) from by decide]
  -- the skipped +1 if
  rw [cons, If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [lookup_insert_self_fin]
  try rw [show fromBool ((1 : UInt256) = 0) = (0 : UInt256) from by decide]
  try simp only [show decide ((1 : UInt256) = 0) = false from by decide]
  try simp only [show fromBool false = (0 : UInt256) from by decide]
  try simp only [List.head!]
  try simp only [reduceIte]
  try rw [if_neg (by exact fun h => h rfl)]
  -- chunk A
  rw [cons]
  rw [format_allocA_arm (C := C)
    (by rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        rw [lookup_ok_evm _ evm]; exact hcJ)
    hf1a hf2a]
  -- chunk B
  rw [cons]
  rw [format_sliceB_arm (F := evm.mload 64)
    (by rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    hlen32 hp1 hp2]
  -- chunk D
  rw [cons]
  rw [format_tagD_arm (VP := (fmtE1 evm C).mload 64) (B1 := B1)
    (by exact lookup_insert_self_fin)
    h1r]
  -- chunk E
  rw [cons]
  rw [format_byteE_arm (P2 := (fmtE2 evm C).mload 64) (B1 := B1)
    (by rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)]
  -- chunk F
  rw [cons]
  rw [format_copyF_arm (VP := (fmtE1 evm C).mload 64)
      (P2 := (fmtE2 evm C).mload 64) (LN := LN)
    (by rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    hlr]
  -- chunk G
  rw [cons]
  rw [format_addrG_arm (T2 := (fmtE2 evm C).mload 64 + LN) (A := A)
    (by exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        rw [lookup_ok_evm _ evm, ← hJ0']; exact lookup_initcall_2 (by decide))]
  -- chunk H
  rw [cons]
  rw [format_addrH_arm (SA := Fin.shiftLeft A 96)
      (W := ((fmtE2 evm C).mload 64 + LN) + 38)
      (T2 := (fmtE2 evm C).mload 64 + LN) (P2 := (fmtE2 evm C).mload 64)
    (by exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)]
  -- chunk I
  rw [cons]
  rw [format_finalI_arm (L3 := fmtL3 evm C LN) (P2 := (fmtE2 evm C).mload 64)
    (by exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)
    hfI1 hfI2]
  -- ret chunk
  rw [cons, nil]
  rw [cons, nil, Assign']
  simp only [Var', insert_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide),
      lookup_insert_self_fin]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [multifill_cons, multifill_nil, insert_Ok]


end

end generated.L2InteropHandler.L2InteropHandler
