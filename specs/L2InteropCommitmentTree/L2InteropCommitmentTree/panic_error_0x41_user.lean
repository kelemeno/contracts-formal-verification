import Clear.ReasoningPrinciple
import specs.StateOk
import specs.KeccakClean
import specs.KeccakLowSlot
import specs.StorageFrame


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Solidity's `Panic(uint256)` revert with code `0x11` (arithmetic overflow or underflow):

    let split_expr_0 := shl(224, 1313373041)   -- 0x4e487b71, the Panic(uint256) selector
    mstore(0, split_expr_0);  mstore(4, 17)    -- 17 = 0x11
    revert(0, 36)

Closed form rather than an alias, so callers can see that this ALWAYS reverts — which is
what the array-bounds guards need in order to say anything about their panic branch. -/
def A_panic_error_0x41   (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦[],[]⟧
  let m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f
  let a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧
  let b := a🇪⟦EVMState.mstore a.evm 4 65⟧
  let c := b🇪⟦EVMState.evm_revert b.evm 0 36⟧
  (🧟 c)🏪⟦s₀⟧ = s₉

lemma panic_error_0x41_abs_of_concrete {s₀ s₉ : State}  :
  Spec (panic_error_0x41_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_panic_error_0x41  ) s₀ s₉ := by
  unfold panic_error_0x41_concrete_of_code A_panic_error_0x41
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc

/-- **THE OUTPUT IS NEVER A BREAK.**  A revert yields an `Ok` state carrying the reverted
flag, not a control-flow jump, so nothing downstream has to consider a `break` coming out of
a panic.

This is the reusable form the loop `ABreak` obligations need: without it every caller
re-walks the same Ok / OutOfFuel / Checkpoint analysis through this function.

Proved by tracking `isOk` along the chain rather than reducing it to a constructor —
`initcall`, `multifill`, `setEvm` and `setStore` each preserve it, and `not_isOk_of_isBreak`
finishes. -/
lemma panic_error_0x41_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x41 s₀ s₉) : isOk s₉ := by
  unfold A_panic_error_0x41 at h
  subst h
  have hm : isOk (multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] (s₀☎️⟦[],[]⟧)) :=
    isOk_multifill (isOk_initcall_of_isOk hok)
  apply isOk_setStore_of_isOk
  rw [revive_of_ok (by simpa using hm)]
  simpa using hm

lemma panic_error_0x41_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x41 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (panic_error_0x41_isOk hok h)

/-! The array-overflow panic.  Structurally identical to `0x11` and `0x32`: two memory
writes and a revert, which in this model keeps the state `Ok` and merely raises a flag.
So it moves storage, window and the collision bit across untouched. -/

private lemma p41_shape {s₀ s₉ : State} (hok : isOk s₀) (h : A_panic_error_0x41 s₀ s₉) :
    ∃ w : UInt256, s₉.evm
      = EVMState.evm_revert (EVMState.mstore (EVMState.mstore s₀.evm 0 w) 4 65) 0 36 := by
  unfold A_panic_error_0x41 at h
  subst h
  set f := s₀☎️⟦[],[]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f with hmdef
  have hmok : isOk m := by rw [hmdef]; exact isOk_multifill hfok
  set a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧ with hadef
  have haok : isOk a := by rw [hadef]; simpa only [isOk_setEvm] using hmok
  set b := a🇪⟦EVMState.mstore a.evm 4 65⟧ with hbdef
  have hbok : isOk b := by rw [hbdef]; simpa only [isOk_setEvm] using haok
  have hcok : isOk (b🇪⟦EVMState.evm_revert b.evm 0 36⟧) := by
    simpa only [isOk_setEvm] using hbok
  have hev : ((🧟 (b🇪⟦EVMState.evm_revert b.evm 0 36⟧))🏪⟦s₀⟧).evm
      = EVMState.evm_revert b.evm 0 36 := by
    rw [evm_setStore, Clear.evm_reviveJump_of_isOk hcok, Clear.evm_setEvm_of_isOk hbok]
  have hfe : f.evm = s₀.evm := by rw [hfdef]; exact Clear.evm_initcall hok
  have hbe : b.evm = EVMState.mstore (EVMState.mstore s₀.evm 0 (m["split_expr_0"]!!)) 4 65 := by
    rw [hbdef, Clear.evm_setEvm_of_isOk haok, hadef, Clear.evm_setEvm_of_isOk hmok, hfe]
  exact ⟨m["split_expr_0"]!!, by rw [hev, hbe]⟩

/-- **STORAGE FRAME.** -/
lemma panic_error_0x41_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x41 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨w, he⟩ := p41_shape hok h
  rw [he, Clear.StorageFrame.sload_evm_revert, Clear.StorageFrame.sload_mstore,
    Clear.StorageFrame.sload_mstore]

/-- **KECCAK WINDOW.** -/
lemma panic_error_0x41_config {s₀ s₉ : State} (hok : isOk s₀)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_panic_error_0x41 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨w, he⟩ := p41_shape hok h
  rw [he]
  exact ⟨Clear.StorageFrame.rangeInWindow_evm_revert
      (Clear.StorageFrame.rangeInWindow_mstore (Clear.StorageFrame.rangeInWindow_mstore hR)),
    Clear.StorageFrame.cachedInWindow_evm_revert
      (Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore hC))⟩

/-- **CLEAN FLAG.** -/
lemma panic_error_0x41_clean {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x41 s₀ s₉) :
    Clear.KeccakClean.Clean s₉.evm ↔ Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨w, he⟩ := p41_shape hok h
  rw [he, Clear.KeccakClean.clean_evm_revert, Clear.KeccakClean.clean_mstore,
    Clear.KeccakClean.clean_mstore]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
