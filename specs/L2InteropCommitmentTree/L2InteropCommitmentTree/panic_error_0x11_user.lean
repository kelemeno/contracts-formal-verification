import Clear.ReasoningPrinciple
import specs.KeccakClean
import specs.StateOk
import specs.StorageFrame
import specs.KeccakFuel
import specs.KeccakLowSlot


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear Clear.StorageFrame Clear.KeccakLowSlot EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Solidity's `Panic(uint256)` revert with code `0x11` (arithmetic overflow or underflow):

    let split_expr_0 := shl(224, 1313373041)   -- 0x4e487b71, the Panic(uint256) selector
    mstore(0, split_expr_0);  mstore(4, 17)    -- 17 = 0x11
    revert(0, 36)

Closed form rather than an alias, so callers can see that this ALWAYS reverts — which is
what the array-bounds guards need in order to say anything about their panic branch. -/
def A_panic_error_0x11   (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦[],[]⟧
  let m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f
  let a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧
  let b := a🇪⟦EVMState.mstore a.evm 4 17⟧
  let c := b🇪⟦EVMState.evm_revert b.evm 0 36⟧
  (🧟 c)🏪⟦s₀⟧ = s₉

lemma panic_error_0x11_abs_of_concrete {s₀ s₉ : State}  :
  Spec (panic_error_0x11_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_panic_error_0x11  ) s₀ s₉ := by
  unfold panic_error_0x11_concrete_of_code A_panic_error_0x11
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
lemma panic_error_0x11_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x11 s₀ s₉) : isOk s₉ := by
  unfold A_panic_error_0x11 at h
  subst h
  have hm : isOk (multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] (s₀☎️⟦[],[]⟧)) :=
    isOk_multifill (isOk_initcall_of_isOk hok)
  apply isOk_setStore_of_isOk
  rw [revive_of_ok (by simpa using hm)]
  simpa using hm

lemma panic_error_0x11_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x11 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (panic_error_0x11_isOk hok h)


/-- **STORAGE FRAME.**  An arithmetic panic preserves every slot -- same reasoning as
`panic_error_0x32_sload`: memory and the revert flag, never `account_map`. -/
lemma panic_error_0x11_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x11 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  unfold A_panic_error_0x11 at h
  subst h
  set f := s₀☎️⟦[],[]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f with hmdef
  have hmok : isOk m := by rw [hmdef]; exact isOk_multifill hfok
  set a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧ with hadef
  have haok : isOk a := by rw [hadef]; simpa only [isOk_setEvm] using hmok
  set b := a🇪⟦EVMState.mstore a.evm 4 17⟧ with hbdef
  have hbok : isOk b := by rw [hbdef]; simpa only [isOk_setEvm] using haok
  have hcok : isOk (b🇪⟦EVMState.evm_revert b.evm 0 36⟧) := by
    simpa only [isOk_setEvm] using hbok
  simp only [evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hcok, Clear.evm_setEvm_of_isOk hbok,
    Clear.StorageFrame.sload_evm_revert, hbdef, Clear.evm_setEvm_of_isOk haok,
    Clear.StorageFrame.sload_mstore, hadef, Clear.evm_setEvm_of_isOk hmok,
    Clear.StorageFrame.sload_mstore, hfdef, Clear.evm_initcall hok]


/-- **CONFIG FRAME.**  Same as the 0x32 panic: memory and the revert flag only. -/
lemma panic_error_0x11_config {s₀ s₉ : State} (hok : isOk s₀)
    (hR : RangeInWindow s₀.evm) (hC : CachedInWindow s₀.evm)
    (h : A_panic_error_0x11 s₀ s₉) :
    RangeInWindow s₉.evm ∧ CachedInWindow s₉.evm := by
  unfold A_panic_error_0x11 at h
  subst h
  set f := s₀☎️⟦[],[]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f with hmdef
  have hmok : isOk m := by rw [hmdef]; exact isOk_multifill hfok
  set a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧ with hadef
  have haok : isOk a := by rw [hadef]; simpa only [isOk_setEvm] using hmok
  set b := a🇪⟦EVMState.mstore a.evm 4 17⟧ with hbdef
  have hbok : isOk b := by rw [hbdef]; simpa only [isOk_setEvm] using haok
  have hcok : isOk (b🇪⟦EVMState.evm_revert b.evm 0 36⟧) := by
    simpa only [isOk_setEvm] using hbok
  have hev : ((🧟 (b🇪⟦EVMState.evm_revert b.evm 0 36⟧))🏪⟦s₀⟧).evm
      = EVMState.evm_revert b.evm 0 36 := by
    rw [evm_setStore, Clear.evm_reviveJump_of_isOk hcok, Clear.evm_setEvm_of_isOk hbok]
  rw [hev]
  have hfe : f.evm = s₀.evm := by rw [hfdef]; exact Clear.evm_initcall hok
  have hbe : b.evm = EVMState.mstore (EVMState.mstore s₀.evm 0 (m["split_expr_0"]!!)) 4 17 := by
    rw [hbdef, Clear.evm_setEvm_of_isOk haok, hadef, Clear.evm_setEvm_of_isOk hmok, hfe]
  have hRb : RangeInWindow b.evm := by
    rw [hbe]; exact rangeInWindow_mstore (rangeInWindow_mstore hR)
  have hCb : CachedInWindow b.evm := by
    rw [hbe]; exact cachedInWindow_mstore (cachedInWindow_mstore hC)
  exact ⟨rangeInWindow_evm_revert hRb, cachedInWindow_evm_revert hCb⟩

/-- **FUEL FRAME.**  The arithmetic panic spends no pool either -- memory writes and a
revert, neither of which touches `keccak_range` or `used_range`. -/
lemma panic_error_0x11_fuel {k : ℕ} {s₀ s₉ : State} (hok : isOk s₀)
    (hf : Clear.KeccakFuel.Fuel s₀.evm k)
    (h : A_panic_error_0x11 s₀ s₉) : Clear.KeccakFuel.Fuel s₉.evm k := by
  unfold A_panic_error_0x11 at h
  subst h
  set f := s₀☎️⟦[],[]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f with hmdef
  have hmok : isOk m := by rw [hmdef]; exact isOk_multifill hfok
  set a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧ with hadef
  have haok : isOk a := by rw [hadef]; simpa only [isOk_setEvm] using hmok
  set b := a🇪⟦EVMState.mstore a.evm 4 17⟧ with hbdef
  have hbok : isOk b := by rw [hbdef]; simpa only [isOk_setEvm] using haok
  have hcok : isOk (b🇪⟦EVMState.evm_revert b.evm 0 36⟧) := by
    simpa only [isOk_setEvm] using hbok
  have hev : ((🧟 (b🇪⟦EVMState.evm_revert b.evm 0 36⟧))🏪⟦s₀⟧).evm
      = EVMState.evm_revert b.evm 0 36 := by
    rw [evm_setStore, Clear.evm_reviveJump_of_isOk hcok, Clear.evm_setEvm_of_isOk hbok]
  have hfe : f.evm = s₀.evm := by rw [hfdef]; exact Clear.evm_initcall hok
  have hbe : b.evm = EVMState.mstore (EVMState.mstore s₀.evm 0 (m["split_expr_0"]!!)) 4 17 := by
    rw [hbdef, Clear.evm_setEvm_of_isOk haok, hadef, Clear.evm_setEvm_of_isOk hmok, hfe]
  rw [hev, hbe]
  exact Clear.KeccakFuel.Fuel.evm_revert 0 36
    (Clear.KeccakFuel.Fuel.mstore 4 17 (Clear.KeccakFuel.Fuel.mstore 0 _ hf))

/-- **CLEAN FLAG.**  Two memory writes and a revert: no hash, so the flag is untouched. -/
lemma panic_error_0x11_clean {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x11 s₀ s₉) :
    Clear.KeccakClean.Clean s₉.evm ↔ Clear.KeccakClean.Clean s₀.evm := by
  unfold A_panic_error_0x11 at h
  subst h
  set f := s₀☎️⟦[],[]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f with hmdef
  have hmok : isOk m := by rw [hmdef]; exact isOk_multifill hfok
  set a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧ with hadef
  have haok : isOk a := by rw [hadef]; simpa only [isOk_setEvm] using hmok
  set b := a🇪⟦EVMState.mstore a.evm 4 17⟧ with hbdef
  have hbok : isOk b := by rw [hbdef]; simpa only [isOk_setEvm] using haok
  have hcok : isOk (b🇪⟦EVMState.evm_revert b.evm 0 36⟧) := by
    simpa only [isOk_setEvm] using hbok
  have hev : ((🧟 (b🇪⟦EVMState.evm_revert b.evm 0 36⟧))🏪⟦s₀⟧).evm
      = EVMState.evm_revert b.evm 0 36 := by
    rw [evm_setStore, Clear.evm_reviveJump_of_isOk hcok, Clear.evm_setEvm_of_isOk hbok]
  have hfe : f.evm = s₀.evm := by rw [hfdef]; exact Clear.evm_initcall hok
  have hbe : b.evm = EVMState.mstore (EVMState.mstore s₀.evm 0 (m["split_expr_0"]!!)) 4 17 := by
    rw [hbdef, Clear.evm_setEvm_of_isOk haok, hadef, Clear.evm_setEvm_of_isOk hmok, hfe]
  rw [hev, Clear.KeccakClean.clean_evm_revert, hbe, Clear.KeccakClean.clean_mstore,
    Clear.KeccakClean.clean_mstore]

/-- **ACCOUNT FRAME.**  Memory writes and a revert leave the account map alone. -/
lemma panic_error_0x11_account {s₀ s₉ : State} {addr : Address} (hok : isOk s₀)
    (h : A_panic_error_0x11 s₀ s₉) :
    Clear.EVMState.lookupAccount s₉.evm addr = Clear.EVMState.lookupAccount s₀.evm addr := by
  unfold A_panic_error_0x11 at h
  subst h
  set f := s₀☎️⟦[],[]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f with hmdef
  have hmok : isOk m := by rw [hmdef]; exact isOk_multifill hfok
  set a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧ with hadef
  have haok : isOk a := by rw [hadef]; simpa only [isOk_setEvm] using hmok
  set b := a🇪⟦EVMState.mstore a.evm 4 17⟧ with hbdef
  have hbok : isOk b := by rw [hbdef]; simpa only [isOk_setEvm] using haok
  have hcok : isOk (b🇪⟦EVMState.evm_revert b.evm 0 36⟧) := by
    simpa only [isOk_setEvm] using hbok
  have hev : ((🧟 (b🇪⟦EVMState.evm_revert b.evm 0 36⟧))🏪⟦s₀⟧).evm
      = EVMState.evm_revert b.evm 0 36 := by
    rw [evm_setStore, Clear.evm_reviveJump_of_isOk hcok, Clear.evm_setEvm_of_isOk hbok]
  have hfe : f.evm = s₀.evm := by rw [hfdef]; exact Clear.evm_initcall hok
  have hbe : b.evm = EVMState.mstore (EVMState.mstore s₀.evm 0 (m["split_expr_0"]!!)) 4 17 := by
    rw [hbdef, Clear.evm_setEvm_of_isOk haok, hadef, Clear.evm_setEvm_of_isOk hmok, hfe]
  rw [hev, Clear.StorageFrame.lookupAccount_evm_revert, hbe,
    Clear.StorageFrame.lookupAccount_mstore, Clear.StorageFrame.lookupAccount_mstore]

/-- **EXECUTION ENVIRONMENT FRAME.**  Travels with the account frame: an account witness
names its address as `code_owner`, so both halves are needed to carry one across a call. -/
lemma panic_error_0x11_env {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x11 s₀ s₉) :
    s₉.evm.execution_env = s₀.evm.execution_env := by
  unfold A_panic_error_0x11 at h
  subst h
  set f := s₀☎️⟦[],[]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f with hmdef
  have hmok : isOk m := by rw [hmdef]; exact isOk_multifill hfok
  set a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧ with hadef
  have haok : isOk a := by rw [hadef]; simpa only [isOk_setEvm] using hmok
  set b := a🇪⟦EVMState.mstore a.evm 4 17⟧ with hbdef
  have hbok : isOk b := by rw [hbdef]; simpa only [isOk_setEvm] using haok
  have hcok : isOk (b🇪⟦EVMState.evm_revert b.evm 0 36⟧) := by
    simpa only [isOk_setEvm] using hbok
  have hev : ((🧟 (b🇪⟦EVMState.evm_revert b.evm 0 36⟧))🏪⟦s₀⟧).evm
      = EVMState.evm_revert b.evm 0 36 := by
    rw [evm_setStore, Clear.evm_reviveJump_of_isOk hcok, Clear.evm_setEvm_of_isOk hbok]
  have hfe : f.evm = s₀.evm := by rw [hfdef]; exact Clear.evm_initcall hok
  have hbe : b.evm = EVMState.mstore (EVMState.mstore s₀.evm 0 (m["split_expr_0"]!!)) 4 17 := by
    rw [hbdef, Clear.evm_setEvm_of_isOk haok, hadef, Clear.evm_setEvm_of_isOk hmok, hfe]
  rw [hev, Clear.StorageFrame.execution_env_evm_revert, hbe,
    Clear.StorageFrame.execution_env_mstore, Clear.StorageFrame.execution_env_mstore]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
