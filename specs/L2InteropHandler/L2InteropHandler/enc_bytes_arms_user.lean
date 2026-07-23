import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.L2InteropHandler.L2InteropHandler.mem_helpers_user
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes

/-
  `abi_encode_bytes` CLOSED FORM (L2InteropHandler) — the byte-array encoder
  used (twice) by the dispatch encoder `abi_encode_bytes32_bytes_bytes`.

  Branch-free: write the length word at `pos`, copy the payload (A3 no-op),
  zero the word after the payload, return the word-padded end pointer.
  Everything symbolic — no readbacks, no guards.  Axiom-free.
-/

namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

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

private lemma lookup_ok_evm {σ : VarStore} {k : Identifier} (e e' : EVMState) :
    (Ok e σ)[k]!! = (Ok e' σ)[k]!! := rfl

private lemma reviveJump_of_isOk {s : State} (h : isOk s) : 🧟 s = s := by
  obtain ⟨evm₀, store, rfl⟩ := State_of_isOk h; rfl

/-! ### The three chunks -/

@[reducible] private def encBytesChunk1 : Stmt := <s
  {
      let length := mload(value)
      mstore(pos, length)
      let split_expr_0 := add(pos, 32)
      let split_expr_1 := add(value, 32)
      mcopy(split_expr_0, split_expr_1, length)
  }
>

@[reducible] private def encBytesChunk2 : Stmt := <s
  {
      let split_expr_2 := add(pos, length)
      let split_expr_3 := add(split_expr_2, 32)
      mstore(split_expr_3, 0)
      let split_expr_4 := add(length, 31)
      let split_expr_5 := not(31)
  }
>

@[reducible] private def encBytesChunk3 : Stmt := <s
  {
      let split_expr_6 := and(split_expr_4, split_expr_5)
      let split_expr_7 := add(pos, split_expr_6)
      end_clear_sanitised_hrafn := add(split_expr_7, 32)
  }
>

private lemma encBytes1_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {V P : Literal}
    (hv : (Ok evm σ)["value"]!! = V)
    (hp : (Ok evm σ)["pos"]!! = P) :
    exec (fuel+1) encBytesChunk1 (Ok evm σ)
      = Ok (evm.mstore P (evm.mload V))
          (((σ.insert "length" (evm.mload V)).insert
            "split_expr_0" (P + 32)).insert
            "split_expr_1" (V + 32)) := by
  unfold encBytesChunk1
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMload',
             evm_Ok, insert_Ok]
  rw [hv]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), hp]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_ok_evm _ evm, hp]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_ok_evm _ evm, hv]
  rw [cons, nil, ExprStmtCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [show (Ok (evm.mstore P (evm.mload V))
        (Finmap.insert "split_expr_1" (V + 32)
          (Finmap.insert "split_expr_0" (P + 32)
            (Finmap.insert "length" (evm.mload V) σ))))["split_expr_0"]!!
      = P + 32 from by
    rw [lookup_insert_ne_fin (by decide)]; exact lookup_insert_self_fin]
  rw [show (Ok (evm.mstore P (evm.mload V))
        (Finmap.insert "split_expr_1" (V + 32)
          (Finmap.insert "split_expr_0" (P + 32)
            (Finmap.insert "length" (evm.mload V) σ))))["split_expr_1"]!!
      = V + 32 from lookup_insert_self_fin]
  rw [show (Ok (evm.mstore P (evm.mload V))
        (Finmap.insert "split_expr_1" (V + 32)
          (Finmap.insert "split_expr_0" (P + 32)
            (Finmap.insert "length" (evm.mload V) σ))))["length"]!!
      = evm.mload V from by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin]
  rw [mcopy_call]

private lemma encBytes2_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {P L : Literal}
    (hp : (Ok evm σ)["pos"]!! = P)
    (hl : (Ok evm σ)["length"]!! = L) :
    exec (fuel+1) encBytesChunk2 (Ok evm σ)
      = Ok (evm.mstore (P + L + 32) 0)
          (((((σ.insert "split_expr_2" (P + L)).insert
            "split_expr_3" (P + L + 32)).insert
            "split_expr_4" (L + 31)).insert
            "split_expr_5" (Clear.UInt256.lnot 31))) := by
  unfold encBytesChunk2
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [hp, hl]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_self_fin]
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_ok_evm _ evm, hl]
  rw [cons, nil, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMNot',
             insert_Ok]

private lemma encBytes3_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {P L4 : Literal}
    (hp : (Ok evm σ)["pos"]!! = P)
    (h4 : (Ok evm σ)["split_expr_4"]!! = L4)
    (h5 : (Ok evm σ)["split_expr_5"]!! = Clear.UInt256.lnot 31) :
    exec (fuel+1) encBytesChunk3 (Ok evm σ)
      = Ok evm (((σ.insert "split_expr_6" (Fin.land L4 (Clear.UInt256.lnot 31))).insert
          "split_expr_7" (P + Fin.land L4 (Clear.UInt256.lnot 31))).insert
          "end_clear_sanitised_hrafn"
          (P + Fin.land L4 (Clear.UInt256.lnot 31) + 32)) := by
  unfold encBytesChunk3
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAnd',
             insert_Ok]
  rw [h4, h5]
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), hp]
  rw [cons, nil, AssignPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_self_fin]

end

end generated.L2InteropHandler.L2InteropHandler
