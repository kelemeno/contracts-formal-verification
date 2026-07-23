import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.L2InteropHandler.L2InteropHandler.mem_helpers_user

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

end

end generated.L2InteropHandler.L2InteropHandler
