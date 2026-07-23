import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.L2InteropHandler.L2InteropHandler.mem_helpers_user
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes32_bytes_bytes

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

/-! ### The assembly -/

/-- **`abi_encode_bytes` closed form**: write the length word at `pos`, copy
the payload (A3 no-op), zero the word after, return `pos + pad(len) + 32`. -/
lemma abi_encode_bytes_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {V P : Literal}
    {t : Identifier} :
    execCall (fuel+1) abi_encode_bytes [t] (Ok evm store, [V, P])
      = Ok ((evm.mstore P (evm.mload V)).mstore (P + evm.mload V + 32) 0)
          (store.insert t
            (P + Fin.land (evm.mload V + 31) (Clear.UInt256.lnot 31) + 32)) := by
  unfold execCall call abi_encode_bytes
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  have hok0 : isOk ((Ok evm store)☎️⟦["value", "pos"], [V, P]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["value", "pos"], [V, P]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  set J := (Ok evm store)☎️⟦["value", "pos"], [V, P]⟧
  obtain ⟨e0, σ0, hJ0⟩ := State_of_isOk hok0
  have he0 : e0 = evm := by
    have h := congrArg State.evm hJ0
    rw [hevm0] at h
    exact h.symm
  have hJ0' : J = Ok evm σ0 := by rw [hJ0, he0]
  rw [hJ0']
  -- chunk 1
  rw [cons]
  rw [encBytes1_arm (V := V) (P := P)
    (by rw [← hJ0']; exact lookup_initcall_1)
    (by rw [← hJ0']; exact lookup_initcall_2 (by decide))]
  -- chunk 2
  rw [cons]
  rw [encBytes2_arm (P := P) (L := evm.mload V)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_ok_evm _ evm, ← hJ0']
        exact lookup_initcall_2 (by decide))
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
        exact lookup_insert_self_fin)]
  -- chunk 3
  rw [cons, nil]
  rw [encBytes3_arm (P := P) (L4 := evm.mload V + 31)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_ok_evm _ evm, ← hJ0']
        exact lookup_initcall_2 (by decide))
    (by rw [lookup_insert_ne_fin (by decide)]; exact lookup_insert_self_fin)
    (by exact lookup_insert_self_fin)]
  -- the ret lookup and the wrapper
  rw [lookup_insert_self_fin]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [multifill_cons, multifill_nil, insert_Ok]

/-! ### The dispatch encoder: `abi_encode_bytes32_bytes_bytes` -/

@[reducible] private def enc3Chunk1 : Stmt := <s
  {
      mstore(headStart, value0)
      let split_expr_0 := add(headStart, 32)
      mstore(split_expr_0, 96)
      let split_expr_1 := add(headStart, 96)
      let tail_1 := abi_encode_bytes(value1, split_expr_1)
  }
>

@[reducible] private def enc3Chunk2 : Stmt := <s
  {
      let split_expr_2 := add(headStart, 64)
      let split_expr_3 := sub(tail_1, headStart)
      mstore(split_expr_2, split_expr_3)
      tail := abi_encode_bytes(value2, tail_1)
  }
>

private lemma enc3Chunk1_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {H W0 V1 : Literal}
    (hh : (Ok evm σ)["headStart"]!! = H)
    (h0 : (Ok evm σ)["value0"]!! = W0)
    (h1 : (Ok evm σ)["value1"]!! = V1) :
    exec (fuel+1) enc3Chunk1 (Ok evm σ)
      = Ok ((((evm.mstore H W0).mstore (H + 32) 96).mstore (H + 96)
            (((evm.mstore H W0).mstore (H + 32) 96).mload V1)).mstore
            ((H + 96) + ((evm.mstore H W0).mstore (H + 32) 96).mload V1 + 32) 0)
          (((σ.insert "split_expr_0" (H + 32)).insert
            "split_expr_1" (H + 96)).insert
            "tail_1" ((H + 96)
              + Fin.land (((evm.mstore H W0).mstore (H + 32) 96).mload V1 + 31)
                (Clear.UInt256.lnot 31) + 32)) := by
  unfold enc3Chunk1
  -- mstore(headStart, value0)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [h0, hh]
  -- let split_expr_0 := add(headStart, 32)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_ok_evm _ evm, hh]
  -- mstore(split_expr_0, 96)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  -- let split_expr_1 := add(headStart, 96)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_ok_evm _ evm, hh]
  -- let tail_1 := abi_encode_bytes(value1, split_expr_1)
  rw [cons, nil, LetCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_ok_evm _ evm, h1]
  rw [abi_encode_bytes_call]

private lemma enc3Chunk2_arm
    {evm : EVMState} {σ : VarStore} {fuel : ℕ} {H T1 V2 : Literal}
    (hh : (Ok evm σ)["headStart"]!! = H)
    (ht1 : (Ok evm σ)["tail_1"]!! = T1)
    (h2 : (Ok evm σ)["value2"]!! = V2) :
    exec (fuel+1) enc3Chunk2 (Ok evm σ)
      = Ok (((evm.mstore (H + 64) (T1 - H)).mstore T1
            ((evm.mstore (H + 64) (T1 - H)).mload V2)).mstore
            (T1 + (evm.mstore (H + 64) (T1 - H)).mload V2 + 32) 0)
          (((σ.insert "split_expr_2" (H + 64)).insert
            "split_expr_3" (T1 - H)).insert
            "tail" (T1
              + Fin.land ((evm.mstore (H + 64) (T1 - H)).mload V2 + 31)
                (Clear.UInt256.lnot 31) + 32)) := by
  unfold enc3Chunk2
  -- let split_expr_2 := add(headStart, 64)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMAdd',
             insert_Ok]
  rw [hh]
  -- let split_expr_3 := sub(tail_1, headStart)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMSub',
             insert_Ok]
  rw [lookup_insert_ne_fin (by decide), ht1]
  rw [lookup_insert_ne_fin (by decide), hh]
  -- mstore(split_expr_2, split_expr_3)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  rw [lookup_insert_self_fin]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_self_fin]
  -- tail := abi_encode_bytes(value2, tail_1)
  rw [cons, nil, AssignCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             evm_Ok, setEvm_Ok]
  rw [show (Ok ((evm.mstore (H + 64) (T1 - H)))
        (Finmap.insert "split_expr_3" (T1 - H)
          (Finmap.insert "split_expr_2" (H + 64) σ)))["tail_1"]!!
      = T1 from by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_ok_evm _ evm]
    exact ht1]
  rw [show (Ok ((evm.mstore (H + 64) (T1 - H)))
        (Finmap.insert "split_expr_3" (T1 - H)
          (Finmap.insert "split_expr_2" (H + 64) σ)))["value2"]!!
      = V2 from by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_ok_evm _ evm]
    exact h2]
  rw [abi_encode_bytes_call]

/-- Stages of the dispatch encoder. -/
@[reducible] def enc3Head (evm : EVMState) (H W0 : Literal) : EVMState :=
  (evm.mstore H W0).mstore (H + 32) 96

@[reducible] def enc3T1 (evm : EVMState) (H W0 V1 : Literal) : Literal :=
  (H + 96) + Fin.land ((enc3Head evm H W0).mload V1 + 31) (Clear.UInt256.lnot 31) + 32

@[reducible] def enc3Mid (evm : EVMState) (H W0 V1 : Literal) : EVMState :=
  ((enc3Head evm H W0).mstore (H + 96) ((enc3Head evm H W0).mload V1)).mstore
    ((H + 96) + (enc3Head evm H W0).mload V1 + 32) 0

@[reducible] def enc3Pre2 (evm : EVMState) (H W0 V1 : Literal) : EVMState :=
  (enc3Mid evm H W0 V1).mstore (H + 64) (enc3T1 evm H W0 V1 - H)

/-- **`abi_encode_bytes32_bytes_bytes` closed form**: head word, fixed offset
96, first byte-array at `H + 96`, back-patched second offset, second
byte-array at the running tail; returns the final tail. -/
lemma abi_encode3_call
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    {H W0 V1 V2 : Literal} {t : Identifier} :
    execCall (fuel+1) abi_encode_bytes32_bytes_bytes [t]
        (Ok evm store, [H, W0, V1, V2])
      = Ok (((enc3Pre2 evm H W0 V1).mstore (enc3T1 evm H W0 V1)
            ((enc3Pre2 evm H W0 V1).mload V2)).mstore
            (enc3T1 evm H W0 V1 + (enc3Pre2 evm H W0 V1).mload V2 + 32) 0)
          (store.insert t
            (enc3T1 evm H W0 V1
              + Fin.land ((enc3Pre2 evm H W0 V1).mload V2 + 31)
                (Clear.UInt256.lnot 31) + 32)) := by
  unfold execCall call abi_encode_bytes32_bytes_bytes
  simp only [params, body, rets, multifill', mkOk_initcall_Ok,
             List.map_nil, List.map_cons]
  have hok0 : isOk ((Ok evm store)☎️⟦["headStart", "value0", "value1", "value2"],
      [H, W0, V1, V2]⟧) :=
    isOk_initcall_of_isOk trivial
  have hevm0 : ((Ok evm store)☎️⟦["headStart", "value0", "value1", "value2"],
      [H, W0, V1, V2]⟧).evm = evm := by
    unfold initcall; simp only [evm_multifill, evm_setStore]; rfl
  set J := (Ok evm store)☎️⟦["headStart", "value0", "value1", "value2"],
      [H, W0, V1, V2]⟧
  obtain ⟨e0, σ0, hJ0⟩ := State_of_isOk hok0
  have he0 : e0 = evm := by
    have h := congrArg State.evm hJ0
    rw [hevm0] at h
    exact h.symm
  have hJ0' : J = Ok evm σ0 := by rw [hJ0, he0]
  rw [hJ0']
  -- chunk 1
  rw [cons]
  rw [enc3Chunk1_arm (H := H) (W0 := W0) (V1 := V1)
    (by rw [← hJ0']; exact lookup_initcall_1)
    (by rw [← hJ0']; exact lookup_initcall_2 (by decide))
    (by rw [← hJ0']; exact lookup_initcall_3 (by decide) (by decide))]
  -- chunk 2
  rw [cons, nil]
  rw [enc3Chunk2_arm (H := H)
    (T1 := (H + 96) + Fin.land (((evm.mstore H W0).mstore (H + 32) 96).mload V1 + 31)
      (Clear.UInt256.lnot 31) + 32)
    (V2 := V2)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_ok_evm _ evm, ← hJ0']
        exact lookup_initcall_1)
    (by exact lookup_insert_self_fin)
    (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
            lookup_insert_ne_fin (by decide), lookup_ok_evm _ evm, ← hJ0']
        exact lookup_initcall_4 (by decide) (by decide) (by decide))]
  -- the ret lookup and the wrapper
  rw [lookup_insert_self_fin]
  rw [reviveJump_of_isOk (by trivial)]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [multifill_cons, multifill_nil, insert_Ok]

end

end generated.L2InteropHandler.L2InteropHandler
