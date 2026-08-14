import Clear.ReasoningPrinciple
import specs.StateOk
import specs.StorageFrame
import specs.KeccakFuel
import specs.KeccakLowSlot


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear Clear.StorageFrame Clear.KeccakLowSlot EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Solidity's `Panic(uint256)` revert with code `0x32` (array index out of bounds):

    let split_expr_0 := shl(224, 1313373041)   -- 0x4e487b71, the Panic(uint256) selector
    mstore(0, split_expr_0);  mstore(4, 50)    -- 50 = 0x32
    revert(0, 36)

Closed form rather than an alias, so callers can see that this ALWAYS reverts — which is
what the array-bounds guards need in order to say anything about their panic branch. -/
def A_panic_error_0x32   (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦[],[]⟧
  let m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f
  let a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧
  let b := a🇪⟦EVMState.mstore a.evm 4 50⟧
  let c := b🇪⟦EVMState.evm_revert b.evm 0 36⟧
  (🧟 c)🏪⟦s₀⟧ = s₉

lemma panic_error_0x32_abs_of_concrete {s₀ s₉ : State}  :
  Spec (panic_error_0x32_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_panic_error_0x32  ) s₀ s₉ := by
  unfold panic_error_0x32_concrete_of_code A_panic_error_0x32
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
lemma panic_error_0x32_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x32 s₀ s₉) : isOk s₉ := by
  unfold A_panic_error_0x32 at h
  subst h
  have hm : isOk (multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] (s₀☎️⟦[],[]⟧)) :=
    isOk_multifill (isOk_initcall_of_isOk hok)
  apply isOk_setStore_of_isOk
  rw [revive_of_ok (by simpa using hm)]
  simpa using hm

lemma panic_error_0x32_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x32 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (panic_error_0x32_isOk hok h)


/-- **STORAGE FRAME.**  A panic writes the selector to memory and reverts; storage is
untouched, so `sload` reads the same before and after.

Clear models a revert as a FLAG (see `Clear.StorageFrame.sload_evm_revert`), so this says
nothing about the EVM's real undo semantics -- only that this state carries the same
storage it was given. -/
lemma panic_error_0x32_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x32 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  unfold A_panic_error_0x32 at h
  subst h
  set f := s₀☎️⟦[],[]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f with hmdef
  have hmok : isOk m := by rw [hmdef]; exact isOk_multifill hfok
  set a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧ with hadef
  have haok : isOk a := by rw [hadef]; simpa only [isOk_setEvm] using hmok
  set b := a🇪⟦EVMState.mstore a.evm 4 50⟧ with hbdef
  have hbok : isOk b := by rw [hbdef]; simpa only [isOk_setEvm] using haok
  have hcok : isOk (b🇪⟦EVMState.evm_revert b.evm 0 36⟧) := by
    simpa only [isOk_setEvm] using hbok
  simp only [evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hcok, Clear.evm_setEvm_of_isOk hbok,
    Clear.StorageFrame.sload_evm_revert, hbdef, Clear.evm_setEvm_of_isOk haok,
    Clear.StorageFrame.sload_mstore, hadef, Clear.evm_setEvm_of_isOk hmok,
    Clear.StorageFrame.sload_mstore, hfdef, Clear.evm_initcall hok]


/-- **CONFIG FRAME.**  A panic writes memory and reverts; the keccak window is untouched. -/
lemma panic_error_0x32_config {s₀ s₉ : State} (hok : isOk s₀)
    (hR : RangeInWindow s₀.evm) (hC : CachedInWindow s₀.evm)
    (h : A_panic_error_0x32 s₀ s₉) :
    RangeInWindow s₉.evm ∧ CachedInWindow s₉.evm := by
  unfold A_panic_error_0x32 at h
  subst h
  set f := s₀☎️⟦[],[]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f with hmdef
  have hmok : isOk m := by rw [hmdef]; exact isOk_multifill hfok
  set a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧ with hadef
  have haok : isOk a := by rw [hadef]; simpa only [isOk_setEvm] using hmok
  set b := a🇪⟦EVMState.mstore a.evm 4 50⟧ with hbdef
  have hbok : isOk b := by rw [hbdef]; simpa only [isOk_setEvm] using haok
  have hcok : isOk (b🇪⟦EVMState.evm_revert b.evm 0 36⟧) := by
    simpa only [isOk_setEvm] using hbok
  have hev : ((🧟 (b🇪⟦EVMState.evm_revert b.evm 0 36⟧))🏪⟦s₀⟧).evm
      = EVMState.evm_revert b.evm 0 36 := by
    rw [evm_setStore, Clear.evm_reviveJump_of_isOk hcok, Clear.evm_setEvm_of_isOk hbok]
  rw [hev]
  have hfe : f.evm = s₀.evm := by rw [hfdef]; exact Clear.evm_initcall hok
  have hbe : b.evm = EVMState.mstore (EVMState.mstore s₀.evm 0 (m["split_expr_0"]!!)) 4 50 := by
    rw [hbdef, Clear.evm_setEvm_of_isOk haok, hadef, Clear.evm_setEvm_of_isOk hmok, hfe]
  have hRb : RangeInWindow b.evm := by
    rw [hbe]; exact rangeInWindow_mstore (rangeInWindow_mstore hR)
  have hCb : CachedInWindow b.evm := by
    rw [hbe]; exact cachedInWindow_mstore (cachedInWindow_mstore hC)
  exact ⟨rangeInWindow_evm_revert hRb, cachedInWindow_evm_revert hCb⟩

/-- **ACCOUNT FRAME.**  A panic writes memory and reverts, so the account map and the
execution environment come through untouched -- which is what keeps a "the write reads
back" hypothesis alive across a call that MIGHT panic.

Same chain as `_sload`; the storage-vs-account difference is only which frame lemma
retires each step. -/
lemma panic_error_0x32_account {addr : Address} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x32 s₀ s₉) :
    Clear.EVMState.lookupAccount s₉.evm addr = Clear.EVMState.lookupAccount s₀.evm addr ∧
      s₉.evm.execution_env = s₀.evm.execution_env := by
  unfold A_panic_error_0x32 at h
  subst h
  set f := s₀☎️⟦[],[]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f with hmdef
  have hmok : isOk m := by rw [hmdef]; exact isOk_multifill hfok
  set a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧ with hadef
  have haok : isOk a := by rw [hadef]; simpa only [isOk_setEvm] using hmok
  set b := a🇪⟦EVMState.mstore a.evm 4 50⟧ with hbdef
  have hbok : isOk b := by rw [hbdef]; simpa only [isOk_setEvm] using haok
  have hcok : isOk (b🇪⟦EVMState.evm_revert b.evm 0 36⟧) := by
    simpa only [isOk_setEvm] using hbok
  simp only [evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hcok, Clear.evm_setEvm_of_isOk hbok,
    Clear.StorageFrame.lookupAccount_evm_revert,
    Clear.StorageFrame.execution_env_evm_revert, hbdef,
    Clear.evm_setEvm_of_isOk haok, Clear.StorageFrame.lookupAccount_mstore,
    Clear.StorageFrame.execution_env_mstore, hadef, Clear.evm_setEvm_of_isOk hmok,
    Clear.StorageFrame.lookupAccount_mstore, Clear.StorageFrame.execution_env_mstore,
    hfdef, Clear.evm_initcall hok]
  exact ⟨rfl, rfl⟩

/-- **FUEL FRAME.**  A panic spends no pool: it writes memory and reverts, and neither
touches `keccak_range` or `used_range`.  So a caller's hash budget survives the branch it
hopes never to take. -/
lemma panic_error_0x32_fuel {k : ℕ} {s₀ s₉ : State} (hok : isOk s₀)
    (hf : Clear.KeccakFuel.Fuel s₀.evm k)
    (h : A_panic_error_0x32 s₀ s₉) : Clear.KeccakFuel.Fuel s₉.evm k := by
  unfold A_panic_error_0x32 at h
  subst h
  set f := s₀☎️⟦[],[]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f with hmdef
  have hmok : isOk m := by rw [hmdef]; exact isOk_multifill hfok
  set a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧ with hadef
  have haok : isOk a := by rw [hadef]; simpa only [isOk_setEvm] using hmok
  set b := a🇪⟦EVMState.mstore a.evm 4 50⟧ with hbdef
  have hbok : isOk b := by rw [hbdef]; simpa only [isOk_setEvm] using haok
  have hcok : isOk (b🇪⟦EVMState.evm_revert b.evm 0 36⟧) := by
    simpa only [isOk_setEvm] using hbok
  simp only [evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hcok, Clear.evm_setEvm_of_isOk hbok]
  refine Clear.KeccakFuel.Fuel.evm_revert 0 36 ?_
  rw [hbdef, Clear.evm_setEvm_of_isOk haok]
  refine Clear.KeccakFuel.Fuel.mstore 4 50 ?_
  rw [hadef, Clear.evm_setEvm_of_isOk hmok]
  refine Clear.KeccakFuel.Fuel.mstore 0 _ ?_
  rw [hfdef, Clear.evm_initcall hok]
  exact hf

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
