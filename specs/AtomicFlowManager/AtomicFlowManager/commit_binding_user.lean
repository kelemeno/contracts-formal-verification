import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.KeccakInjective
import specs.AtomicFlowManager.AtomicFlowManager.imt_leafhash_user
import generated.AtomicFlowManager.AtomicFlowManager.fun_commitValue

/-
  COMMIT-VALUE CLOSED FORM + BINDING (A6′) — the tree leaf value pins the
  (flowId, bundleHash) pair.

  `commitValue(flowId, specHash) = keccak256(abi.encode(TAG, flowId, specHash))`
  is the ONLY thing the interop commitment tree stores per flow leg: `append`
  inserts it on deposit, `requireFlowFinalized` proves its membership for
  delivery, `authorizeRefund` proves its absence for reclaim.

  This file gives `fun_commitValue` its closed form (`commitValue_call_acc` —
  the pure `commitValueOut`, a keccak over the 3-word scratch
  `TAG ‖ flowId ‖ specHash`), and proves the injectivity direction
  (`commitValueOut_inj`): two collision-free commit values that are EQUAL
  carry the same `flowId` and the same `specHash`.  So a membership or
  absence result for one leg can never stand in for another flow or another
  bundle — the identification chain becomes
  root → leaf hash → leaf fields → commit value → (flowId, bundleHash).

  Trusted base: `Clear.KeccakInjective.keccak256_inj` (A6′) for the binding;
  the closed form itself is axiom-free.
-/

namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism Clear.KeccakInjective

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-! ### Local copies of the state-plumbing helpers (private in
`imt_leafhash_user`) -/

@[simp] private lemma insert_Ok {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

private lemma evm_Ok {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

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

private lemma setEvm_Ok {e E : EVMState} {σ : VarStore} :
    (Ok e σ).setEvm E = Ok E σ := rfl

private lemma primCall_keccakOut {s : State} {a b : Literal} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (keccakOut s.evm a b).2, [(keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

/-- The atomic-commit leaf domain tag: `shl(226, 219235539)` — the constant
`ATOMIC_COMMIT_LEAF_TAG` word the encoder writes at `P+32`. -/
def commitTag : UInt256 := Fin.shiftLeft 219235539 226

/-- The evm after `commitValue`'s five memory writes (tag, flowId, specHash,
length word, free-pointer bump). -/
def commitScratchEvm (evm : EVMState) (flowId specHash : UInt256) : EVMState :=
  ((((evm.mstore (evm.mload 64 + 32) commitTag).mstore
      (evm.mload 64 + 64) flowId).mstore
      (evm.mload 64 + 96) specHash).mstore
      (evm.mload 64) 96).mstore 64 (evm.mload 64 + 128)

/-- The commit-value keccak step: hash the 96-byte region at `P+32`, with the
length taken from the scratch read-back `mload(P)`. -/
def commitValueOut (evm : EVMState) (flowId specHash : UInt256) : UInt256 × EVMState :=
  keccakOut (commitScratchEvm evm flowId specHash) (evm.mload 64 + 32)
    ((commitScratchEvm evm flowId specHash).mload (evm.mload 64))

/-! ## The three body blocks, quoted inline (the generated named block defs
are defeq but kernel-expensive to compare; local quotes are syntactically
identical to the `<f>` body elements, so all matching is free) -/

private def commitBlkA : Stmt := <s {
        let expr_1188_mpos := mload(64)
        let _1 := add(expr_1188_mpos, 32)
        let split_expr_0 := shl(226, 219235539)
        mstore(_1, split_expr_0)
        let split_expr_1 := add(expr_1188_mpos, 64)
      }>

private def commitBlkB : Stmt := <s {
        mstore(split_expr_1, var_flowId)
        let split_expr_2 := add(expr_1188_mpos, 96)
        mstore(split_expr_2, var_specHash)
        mstore(expr_1188_mpos, 96)
        finalize_allocation(expr_1188_mpos, 128)
      }>

private def commitBlkC : Stmt := <s {
        let split_expr_3 := mload(expr_1188_mpos)
        var := keccak256(_1, split_expr_3)
      }>

/-! ## Chunk lemmas over the three body blocks -/

open AtomicFlowManager.Common in
/-- Chunk A — free-pointer read, tag constant, tag write. -/
lemma commitValue_chunkA
    {evm : EVMState} {store : VarStore} {fuel : ℕ} :
    exec (fuel+1) commitBlkA (Ok evm store)
      = Ok (evm.mstore (evm.mload 64 + 32) commitTag)
          ((((store.insert "expr_1188_mpos" (evm.mload 64)).insert
              "_1" (evm.mload 64 + 32)).insert "split_expr_0" commitTag).insert
              "split_expr_1" (evm.mload 64 + 64)) := by
  unfold commitBlkA
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMload', EVMAdd', EVMShl', EVMMstore']
  simp only [multifill_cons, multifill_nil]
  have hok0 : isOk (Ok evm store) := trivial
  have hok1 : isOk ((Ok evm store)⟦"expr_1188_mpos" ↦ evm.mload 64⟧) := isOk_insert.mpr hok0
  have r1 : ((Ok evm store)⟦"expr_1188_mpos" ↦ evm.mload 64⟧)["expr_1188_mpos"]!!
      = evm.mload 64 := lookup_insert' hok0
  simp only [evm_insert, evm_Ok]
  rw [r1]
  have hok2 : isOk ((Ok evm store)⟦"expr_1188_mpos" ↦ evm.mload 64⟧⟦"_1" ↦ evm.mload 64 + 32⟧) :=
    isOk_insert.mpr hok1
  have hok3 : isOk ((Ok evm store)⟦"expr_1188_mpos" ↦ evm.mload 64⟧⟦"_1" ↦ evm.mload 64 + 32⟧⟦"split_expr_0" ↦ commitTag⟧) :=
    isOk_insert.mpr hok2
  have r2a : ((Ok evm store)⟦"expr_1188_mpos" ↦ evm.mload 64⟧⟦"_1" ↦ evm.mload 64 + 32⟧⟦"split_expr_0" ↦ commitTag⟧)["_1"]!!
      = evm.mload 64 + 32 := by
    rw [lookup_insert_of_ne (by decide)]
    exact lookup_insert' hok1
  have r2b : ((Ok evm store)⟦"expr_1188_mpos" ↦ evm.mload 64⟧⟦"_1" ↦ evm.mload 64 + 32⟧⟦"split_expr_0" ↦ commitTag⟧)["split_expr_0"]!!
      = commitTag := lookup_insert' hok2
  rw [show Fin.shiftLeft 219235539 226 = commitTag from rfl]
  rw [r2a, r2b]
  set T3 := (Ok evm store)⟦"expr_1188_mpos" ↦ evm.mload 64⟧⟦"_1" ↦ evm.mload 64 + 32⟧⟦"split_expr_0" ↦ commitTag⟧ with hT3
  have hok3' : isOk T3 := by rw [hT3]; exact hok3
  set E1 := evm.mstore (evm.mload 64 + 32) commitTag with hE1
  have hokU1 : isOk (T3🇪⟦E1⟧) := by rw [isOk_setEvm]; exact hok3'
  rw [hT3, hE1]
  simp only [insert_Ok, setEvm_Ok]
  rw [show (Ok (evm.mstore (evm.mload 64 + 32) commitTag)
      (Finmap.insert "split_expr_0" commitTag
        (Finmap.insert "_1" (evm.mload 64 + 32)
          (Finmap.insert "expr_1188_mpos" (evm.mload 64) store))))["expr_1188_mpos"]!!
      = evm.mload 64 from by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin]

open AtomicFlowManager.Common in
/-- Chunk B — the two field writes, the length word, allocation finalize. -/
lemma commitValue_chunkB
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {s1 f P h : Literal}
    (hs1 : (Ok evm store)["split_expr_1"]!! = s1)
    (hf : (Ok evm store)["var_flowId"]!! = f)
    (hP : (Ok evm store)["expr_1188_mpos"]!! = P)
    (hh : (Ok evm store)["var_specHash"]!! = h)
    (hp128 : P.val + 128 ≤ 18446744073709551615) :
    exec (fuel+1) commitBlkB (Ok evm store)
      = Ok ((((evm.mstore s1 f).mstore (P + 96) h).mstore P 96).mstore 64 (P + 128))
          (store.insert "split_expr_2" (P + 96)) := by
  unfold commitBlkB
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall', LetCall', ExprStmtCall',
             evalArgs, evalTail, cons', head', reverse', multifill', PrimCall',
             Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMload', EVMAdd', EVMMstore']
  simp only [multifill_cons, multifill_nil]
  rw [hs1, hf]
  have hok0 : isOk (Ok evm store) := trivial
  simp only [evm_insert, evm_Ok]
  set E1 := evm.mstore s1 f with hE1
  have hokU1 : isOk ((Ok evm store)🇪⟦E1⟧) := by rw [isOk_setEvm]; exact hok0
  have r1a : ((Ok evm store)🇪⟦E1⟧)["expr_1188_mpos"]!! = P := by
    rw [lookup_setEvm_of_isOk hok0]
    exact hP
  have r1b : ((Ok evm store)🇪⟦E1⟧).evm = E1 := evm_setEvm_of_isOk hok0
  rw [r1a, r1b]
  have hokU2 : isOk (((Ok evm store)🇪⟦E1⟧)⟦"split_expr_2" ↦ P + 96⟧) := isOk_insert.mpr hokU1
  have r2a : (((Ok evm store)🇪⟦E1⟧)⟦"split_expr_2" ↦ P + 96⟧)["split_expr_2"]!!
      = P + 96 := lookup_insert' hokU1
  have r2b : (((Ok evm store)🇪⟦E1⟧)⟦"split_expr_2" ↦ P + 96⟧)["var_specHash"]!! = h := by
    rw [lookup_insert_of_ne (by decide), lookup_setEvm_of_isOk hok0]
    exact hh
  rw [r2a, r2b]
  set T2 := ((Ok evm store)🇪⟦E1⟧)⟦"split_expr_2" ↦ P + 96⟧ with hT2
  have hok2' : isOk T2 := by rw [hT2]; exact hokU2
  set E2 := E1.mstore (P + 96) h with hE2
  have hokU3 : isOk (T2🇪⟦E2⟧) := by rw [isOk_setEvm]; exact hok2'
  have r3a : (T2🇪⟦E2⟧)["expr_1188_mpos"]!! = P := by
    rw [lookup_setEvm_of_isOk hok2', hT2, lookup_insert_of_ne (by decide),
        lookup_setEvm_of_isOk hok0]
    exact hP
  have r3b : (T2🇪⟦E2⟧).evm = E2 := evm_setEvm_of_isOk hok2'
  rw [r3a, r3b]
  set E3 := E2.mstore P 96 with hE3
  have hokU4 : isOk ((T2🇪⟦E2⟧)🇪⟦E3⟧) := by rw [isOk_setEvm, isOk_setEvm]; exact hok2'
  have r4 : ((T2🇪⟦E2⟧)🇪⟦E3⟧)["expr_1188_mpos"]!! = P := by
    rw [lookup_setEvm_of_isOk (by rw [isOk_setEvm]; exact hok2')]
    exact r3a
  rw [r4]
  obtain ⟨e6, σ6, h6⟩ := State_of_isOk hokU4
  have he6 : e6 = E3 := by
    have hx := congrArg State.evm h6
    rw [evm_setEvm_of_isOk (by rw [isOk_setEvm]; exact hok2')] at hx
    exact hx.symm
  rw [h6, finalize_allocation_128_call hp128]
  have r5 : ((Ok e6 σ6).setEvm (e6.mstore 64 (P + 128))).evm = e6.mstore 64 (P + 128) :=
    evm_setEvm_of_isOk (by trivial)
  have hσ6 : σ6 = store.insert "split_expr_2" (P + 96) := by
    have hx := congrArg (fun s => match s with | Ok _ σ => σ | _ => σ6) h6
    simp only at hx
    rw [hT2] at hx
    exact hx.symm
  rw [he6, hσ6, hE3, hE2, hE1]
  rfl

open AtomicFlowManager.Common in
/-- Chunk C — the length read-back and the commit keccak. -/
lemma commitValue_chunkC
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {P x : Literal}
    (hP : (Ok evm store)["expr_1188_mpos"]!! = P)
    (hx : (Ok evm store)["_1"]!! = x) :
    exec (fuel+1) commitBlkC (Ok evm store)
      = Ok (keccakOut evm x (evm.mload P)).2
          ((store.insert "split_expr_3" (evm.mload P)).insert
            "var" (keccakOut evm x (evm.mload P)).1) := by
  unfold commitBlkC
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', evalArgs, evalTail, cons', head',
             reverse', multifill', PrimCall', Lit', Var', execPrimCall,
             evalPrimCall, List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMload']
  simp only [multifill_cons, multifill_nil]
  rw [hP]
  have hok0 : isOk (Ok evm store) := trivial
  have hok1 : isOk ((Ok evm store)⟦"split_expr_3" ↦ evm.mload P⟧) := isOk_insert.mpr hok0
  simp only [evm_insert, evm_Ok]
  rw [primCall_keccakOut]
  have r1a : ((Ok evm store)⟦"split_expr_3" ↦ evm.mload P⟧)["_1"]!! = x := by
    rw [lookup_insert_of_ne (by decide)]
    exact hx
  have r1b : ((Ok evm store)⟦"split_expr_3" ↦ evm.mload P⟧)["split_expr_3"]!!
      = evm.mload P := lookup_insert' hok0
  rw [r1a, r1b]
  simp only [multifill_cons, multifill_nil]
  simp only [insert_Ok, setEvm_Ok, evm_Ok]

set_option maxHeartbeats 8000000 in
open AtomicFlowManager.Common in
/-- **`fun_commitValue` closed form** — composed from the three chunk lemmas:
the commit value is the pure `commitValueOut` keccak, the evm advances by the
five scratch writes plus the keccak step. -/
lemma commitValue_call_acc
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {flowId specHash : Literal}
    {v : Identifier}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615) :
    execCall (fuel+1) fun_commitValue [v] (Ok evm store, [flowId, specHash])
      = Ok (commitValueOut evm flowId specHash).2
          (store.insert v (commitValueOut evm flowId specHash).1) := by
  have hbody : fun_commitValue.body
      = [commitBlkA, commitBlkB, commitBlkC] := by
    unfold commitBlkA commitBlkB commitBlkC
    rfl
  have hparams : fun_commitValue.params = ["var_flowId", "var_specHash"] := rfl
  have hrets : fun_commitValue.rets = ["var"] := rfl
  unfold execCall call
  simp only [hparams, hrets, hbody]
  simp only [multifill', mkOk_initcall_Ok, List.map_nil, List.map_cons]
  rw [cons, cons, cons, nil]
  -- expose the initcall state as a literal `Ok`
  have hok0 : isOk ((Ok evm store)☎️⟦["var_flowId", "var_specHash"], [flowId, specHash]⟧) :=
    isOk_initcall_of_isOk trivial
  obtain ⟨e0, σ0, h0⟩ := State_of_isOk hok0
  have hf0 : ((Ok evm store)☎️⟦["var_flowId", "var_specHash"], [flowId, specHash]⟧)["var_flowId"]!!
      = flowId := lookup_initcall_1
  have hh0 : ((Ok evm store)☎️⟦["var_flowId", "var_specHash"], [flowId, specHash]⟧)["var_specHash"]!!
      = specHash := lookup_initcall_2 (by decide)
  have he0 : e0 = evm := by
    have hx := congrArg State.evm h0
    rw [show ((Ok evm store)☎️⟦["var_flowId", "var_specHash"], [flowId, specHash]⟧).evm = evm from by
      unfold initcall; simp only [evm_multifill, evm_setStore]; rfl] at hx
    exact hx.symm
  rw [h0, he0] at hf0 hh0
  simp only [h0, he0]
  -- chunk A
  simp only [commitValue_chunkA]
  -- chunk B (store from chunk A, evm advanced by the tag write)
  set σA := (((σ0.insert "expr_1188_mpos" (evm.mload 64)).insert
      "_1" (evm.mload 64 + 32)).insert "split_expr_0" commitTag).insert
      "split_expr_1" (evm.mload 64 + 64) with hσA
  set EA := evm.mstore (evm.mload 64 + 32) commitTag with hEA
  have hs1 : (Ok EA σA)["split_expr_1"]!! = evm.mload 64 + 64 := by
    rw [hσA]
    exact lookup_insert_self_fin
  have hfA : (Ok EA σA)["var_flowId"]!! = flowId := by
    rw [hσA, lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_ok_evm EA evm]
    exact hf0
  have hPA : (Ok EA σA)["expr_1188_mpos"]!! = evm.mload 64 := by
    rw [hσA, lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  have hhA : (Ok EA σA)["var_specHash"]!! = specHash := by
    rw [hσA, lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_ok_evm EA evm]
    exact hh0
  simp only [commitValue_chunkB hs1 hfA hPA hhA hp]
  -- chunk C (store from chunk B, evm = the full scratch)
  set EB := ((((EA.mstore (evm.mload 64 + 64) flowId).mstore
      (evm.mload 64 + 96) specHash).mstore (evm.mload 64) 96).mstore
      64 (evm.mload 64 + 128)) with hEB
  set σB := σA.insert "split_expr_2" (evm.mload 64 + 96) with hσB
  have hPB : (Ok EB σB)["expr_1188_mpos"]!! = evm.mload 64 := by
    rw [hσB, lookup_insert_ne_fin (by decide), lookup_ok_evm EB EA]
    exact hPA
  have hxB : (Ok EB σB)["_1"]!! = evm.mload 64 + 32 := by
    rw [hσB, lookup_insert_ne_fin (by decide), hσA,
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  simp only [commitValue_chunkC hPB hxB]
  -- rets lookup + call wrappers
  have hvar : (Ok (keccakOut EB (evm.mload 64 + 32) (EB.mload (evm.mload 64))).2
      ((σB.insert "split_expr_3" (EB.mload (evm.mload 64))).insert
        "var" (keccakOut EB (evm.mload 64 + 32) (EB.mload (evm.mload 64))).1))["var"]!!
      = (keccakOut EB (evm.mload 64 + 32) (EB.mload (evm.mload 64))).1 :=
    lookup_insert_self_fin
  simp only [hvar]
  have hokF : isOk (Ok (keccakOut EB (evm.mload 64 + 32) (EB.mload (evm.mload 64))).2
      ((σB.insert "split_expr_3" (EB.mload (evm.mload 64))).insert
        "var" (keccakOut EB (evm.mload 64 + 32) (EB.mload (evm.mload 64))).1)) := trivial
  rw [reviveJump_of_isOk hokF]
  simp only [overwrite?_of_Ok]
  rw [setStore_ok]
  simp only [multifill_cons, multifill_nil, insert_Ok]
  -- align with `commitValueOut`
  have halign : keccakOut EB (evm.mload 64 + 32) (EB.mload (evm.mload 64))
      = commitValueOut evm flowId specHash := by
    rw [hEB, hEA]
    unfold commitValueOut commitScratchEvm
    rfl
  rw [halign]

/-! ## Length read-back and field extraction -/

/-- On the commit scratch, `mload(P)` returns the length word `96`. -/
lemma commitScratch_length_readback
    {evm : EVMState} {flowId specHash : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    (commitScratchEvm evm flowId specHash).mload (evm.mload 64) = 96 := by
  have hms : (commitScratchEvm evm flowId specHash).machine_state
      = ((((evm.machine_state.updateMemory (evm.mload 64 + 32) commitTag).updateMemory
          (evm.mload 64 + 64) flowId).updateMemory
          (evm.mload 64 + 96) specHash).updateMemory
          (evm.mload 64) 96).updateMemory 64 (evm.mload 64 + 128) := rfl
  show (commitScratchEvm evm flowId specHash).machine_state.lookupMemory (evm.mload 64) = 96
  rw [hms]
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have h64v : ((64 : UInt256)).val = 64 := by decide
  rw [lookupMemory_updateMemory_outside _ 64 (evm.mload 64 + 128) (evm.mload 64)
      (by rw [h64v]; norm_num)
      (by omega)
      (by right; rw [h64v]; omega)]
  exact lookupMemory_updateMemory_self' _ (evm.mload 64) 96 (by omega)

/-- The commit value with the length resolved: `commitValue` hashes exactly
the 96-byte region `[P+32, P+128)` of the scratch. -/
lemma commitValueOut_length
    {evm : EVMState} {flowId specHash : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    commitValueOut evm flowId specHash
      = keccakOut (commitScratchEvm evm flowId specHash) (evm.mload 64 + 32) 96 := by
  unfold commitValueOut
  rw [commitScratch_length_readback hp hplow]

private lemma val_add_lit {P q : UInt256} {c : ℕ} (hq : q.val = c)
    (hbound : P.val + c < 2 ^ 256) : (P + q).val = P.val + c := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  rw [Fin.val_add, hq]
  exact Nat.mod_eq_of_lt (by omega)

/-- `Fin.ofNat` of an in-range value is the value. -/
private lemma finOfNat_self (x : UInt256) : (Fin.ofNat x.val : UInt256) = x := by
  apply Fin.ext
  have hv : (Fin.ofNat x.val : UInt256).val = x.val % UInt256.size := rfl
  rw [hv, Nat.mod_eq_of_lt x.isLt]

/-- Element `j` of `mkInterval ms p n` is the word read at byte `p + j`. -/
private lemma mkInterval_get?
    (ms : MachineState) (p n : UInt256) (j : ℕ) (hj : j < n.val) :
    (EVMState.mkInterval ms p n).get? j
      = some (ms.lookupMemory (Fin.ofNat (p.val + j))) := by
  unfold EVMState.mkInterval
  rw [List.get?_map, List.get?_map, List.get?_range' _ _ hj]
  simp only [Option.map_some', one_mul]

/-- `flowId` reads back at `P+64`. -/
private lemma commitScratch_field1
    {evm : EVMState} {flowId specHash : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    (commitScratchEvm evm flowId specHash).machine_state.lookupMemory (evm.mload 64 + 64)
      = flowId := by
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have h32v : ((32 : UInt256)).val = 32 := by decide
  have h96v : ((96 : UInt256)).val = 96 := by decide
  set P := evm.mload 64 with hPdef
  have hP32 : (P + 32).val = P.val + 32 := val_add_lit h32v (by omega)
  have hP64 : (P + 64).val = P.val + 64 := val_add_lit h64v (by omega)
  have hP96 : (P + 96).val = P.val + 96 := val_add_lit h96v (by omega)
  rw [show (commitScratchEvm evm flowId specHash).machine_state
      = ((((evm.machine_state.updateMemory (P + 32) commitTag).updateMemory
          (P + 64) flowId).updateMemory
          (P + 96) specHash).updateMemory
          P 96).updateMemory 64 (P + 128) from rfl]
  rw [lookupMemory_updateMemory_outside _ 64 (P + 128) (P + 64)
      (by rw [h64v]; norm_num) (by omega) (by right; rw [h64v]; omega)]
  rw [lookupMemory_updateMemory_outside _ P 96 (P + 64)
      (by omega) (by omega) (by right; omega)]
  rw [lookupMemory_updateMemory_outside _ (P + 96) _ (P + 64)
      (by omega) (by omega) (by left; omega)]
  exact lookupMemory_updateMemory_self' _ (P + 64) _ (by omega)

/-- `specHash` reads back at `P+96`. -/
private lemma commitScratch_field2
    {evm : EVMState} {flowId specHash : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    (commitScratchEvm evm flowId specHash).machine_state.lookupMemory (evm.mload 64 + 96)
      = specHash := by
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have h32v : ((32 : UInt256)).val = 32 := by decide
  have h96v : ((96 : UInt256)).val = 96 := by decide
  set P := evm.mload 64 with hPdef
  have hP32 : (P + 32).val = P.val + 32 := val_add_lit h32v (by omega)
  have hP64 : (P + 64).val = P.val + 64 := val_add_lit h64v (by omega)
  have hP96 : (P + 96).val = P.val + 96 := val_add_lit h96v (by omega)
  rw [show (commitScratchEvm evm flowId specHash).machine_state
      = ((((evm.machine_state.updateMemory (P + 32) commitTag).updateMemory
          (P + 64) flowId).updateMemory
          (P + 96) specHash).updateMemory
          P 96).updateMemory 64 (P + 128) from rfl]
  rw [lookupMemory_updateMemory_outside _ 64 (P + 128) (P + 96)
      (by rw [h64v]; norm_num) (by omega) (by right; rw [h64v]; omega)]
  rw [lookupMemory_updateMemory_outside _ P 96 (P + 96)
      (by omega) (by omega) (by right; omega)]
  exact lookupMemory_updateMemory_self' _ (P + 96) _ (by omega)

/-- The commit preimage interval: element 32 is `flowId`. -/
private lemma commitInterval_get32
    {evm : EVMState} {flowId specHash : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    (EVMState.mkInterval (commitScratchEvm evm flowId specHash).machine_state
        (evm.mload 64 + 32) 96).get? 32
      = some flowId := by
  have h96v : ((96 : UInt256)).val = 96 := by decide
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have h32v : ((32 : UInt256)).val = 32 := by decide
  set P := evm.mload 64 with hPdef
  have hP32 : (P + 32).val = P.val + 32 := val_add_lit h32v (by omega)
  rw [mkInterval_get? _ _ _ 32 (by rw [h96v]; norm_num)]
  rw [show (P + 32).val + 32 = (P + 64).val from by
    rw [hP32, val_add_lit h64v (by omega)]]
  rw [finOfNat_self]
  rw [commitScratch_field1 hp hplow]

/-- Element 64 is `specHash`. -/
private lemma commitInterval_get64
    {evm : EVMState} {flowId specHash : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    (EVMState.mkInterval (commitScratchEvm evm flowId specHash).machine_state
        (evm.mload 64 + 32) 96).get? 64
      = some specHash := by
  have h96v : ((96 : UInt256)).val = 96 := by decide
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have h32v : ((32 : UInt256)).val = 32 := by decide
  set P := evm.mload 64 with hPdef
  have hP32 : (P + 32).val = P.val + 32 := val_add_lit h32v (by omega)
  rw [mkInterval_get? _ _ _ 64 (by rw [h96v]; norm_num)]
  rw [show (P + 32).val + 64 = (P + 96).val from by
    rw [hP32, val_add_lit h96v (by omega)]]
  rw [finOfNat_self]
  rw [commitScratch_field2 hp hplow]

/-! ## The injectivity theorem -/

/-- **COMMIT-VALUE BINDING (A6′).**  Two collision-free `commitValueOut`
computations with the SAME output carry the SAME `(flowId, specHash)` pair:
a tree leaf value identifies exactly one flow leg.  A membership proof
(delivery, #25) or absence witness (reclaim, #26) for one leg can never be
repurposed for another flow or another bundle. -/
theorem commitValueOut_inj
    {σ₁ σ₂ : EVMState} {flowId₁ specHash₁ flowId₂ specHash₂ : Literal}
    {r : UInt256} {e₁ e₂ : EVMState}
    (h₁ : commitValueOut σ₁ flowId₁ specHash₁ = (r, e₁))
    (h₂ : commitValueOut σ₂ flowId₂ specHash₂ = (r, e₂))
    (hclean₁ : e₁.hash_collision = false)
    (hclean₂ : e₂.hash_collision = false)
    (hp₁ : (σ₁.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow₁ : 96 ≤ (σ₁.mload 64).val)
    (hp₂ : (σ₂.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow₂ : 96 ≤ (σ₂.mload 64).val) :
    flowId₁ = flowId₂ ∧ specHash₁ = specHash₂ := by
  rw [commitValueOut_length hp₁ hplow₁] at h₁
  rw [commitValueOut_length hp₂ hplow₂] at h₂
  have hs₁ : (commitScratchEvm σ₁ flowId₁ specHash₁).keccak256 (σ₁.mload 64 + 32) 96
      = some (r, e₁) := by
    have := keccakOut_some_of_clean (σ := commitScratchEvm σ₁ flowId₁ specHash₁)
      (p := σ₁.mload 64 + 32) (n := 96) (by rw [h₁]; exact hclean₁)
    rw [h₁] at this
    exact this
  have hs₂ : (commitScratchEvm σ₂ flowId₂ specHash₂).keccak256 (σ₂.mload 64 + 32) 96
      = some (r, e₂) := by
    have := keccakOut_some_of_clean (σ := commitScratchEvm σ₂ flowId₂ specHash₂)
      (p := σ₂.mload 64 + 32) (n := 96) (by rw [h₂]; exact hclean₂)
    rw [h₂] at this
    exact this
  refine ⟨?_, ?_⟩
  · by_contra hne
    refine keccak256_inj hs₁ hs₂ ?_ rfl
    intro he
    have h := congrArg (fun l => l.get? 32) he
    simp only [commitInterval_get32 hp₁ hplow₁, commitInterval_get32 hp₂ hplow₂] at h
    exact hne (Option.some.inj h)
  · by_contra hne
    refine keccak256_inj hs₁ hs₂ ?_ rfl
    intro he
    have h := congrArg (fun l => l.get? 64) he
    simp only [commitInterval_get64 hp₁ hplow₁, commitInterval_get64 hp₂ hplow₂] at h
    exact hne (Option.some.inj h)

end

end generated.AtomicFlowManager.AtomicFlowManager
