import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakLowSlot
import specs.KeccakPrimOps
import specs.KeccakDeterminism
import specs.StateOk
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_dataslot_array_bytes32_dyn_storage_ptr_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Data base of a storage array**: `mstore(0, ptr); data := keccak256(0, 32)`.

The array-of-arrays counterpart of the element accessor's base computation -- elements
of the array at `ptr` start at `keccak(ptr)`. -/
def A_array_dataslot_array_bytes32_dyn_storage_ptr (data : Identifier) (ptr : Literal)
    (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["ptr"],[ptr]⟧
  let m := f🇪⟦Clear.EVMState.mstore f.evm 0 (f["ptr"]!!)⟧
  let kk := Clear.State.multifill ["data"] (primCall m .Keccak256 [0, 32]).2
    (primCall m .Keccak256 [0, 32]).1
  s₉ = 🧟kk🏪⟦s₀⟧⟦data ↦ kk["data"]!!⟧

lemma array_dataslot_array_bytes32_dyn_storage_ptr_abs_of_concrete {s₀ s₉ : State} {data ptr} :
  Spec (array_dataslot_array_bytes32_dyn_storage_ptr_concrete_of_code.1 data ptr) s₀ s₉ →
  Spec (A_array_dataslot_array_bytes32_dyn_storage_ptr data ptr) s₀ s₉ := by
  unfold array_dataslot_array_bytes32_dyn_storage_ptr_concrete_of_code A_array_dataslot_array_bytes32_dyn_storage_ptr
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

lemma array_dataslot_array_bytes32_dyn_storage_ptr_isOk {data : Identifier} {ptr : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_array_dataslot_array_bytes32_dyn_storage_ptr data ptr s₀ s₉) : isOk s₉ := by
  subst h
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma array_dataslot_array_bytes32_dyn_storage_ptr_not_break {data : Identifier} {ptr : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_array_dataslot_array_bytes32_dyn_storage_ptr data ptr s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (array_dataslot_array_bytes32_dyn_storage_ptr_isOk hnf h)

/-- **STORAGE FRAME.**  The data-slot helper hashes the array's slot to find where its
elements start; it `mstore`s and hashes and writes NO storage, so every slot reads back
unchanged.  There is no second branch here -- unlike the index accessor, this one has no
bounds check to fail. -/
lemma array_dataslot_array_bytes32_dyn_storage_ptr_sload {data : Identifier}
    {ptr : Literal} {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_array_dataslot_array_bytes32_dyn_storage_ptr data ptr s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  subst h
  set f := s₀☎️⟦["ptr"],[ptr]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := f🇪⟦Clear.EVMState.mstore f.evm 0 (f["ptr"]!!)⟧ with hmdef
  have hmok : isOk m := by rw [hmdef]; simp only [isOk_setEvm]; exact hfok
  simp only [Clear.KeccakPrimOps.primCall_keccakOut, multifill_cons, multifill_nil, evm_insert, evm_setStore]
  have hXok : isOk (m🇪⟦(Clear.KeccakDeterminism.keccakOut m.evm 0 32).2⟧⟦"data" ↦
      (Clear.KeccakDeterminism.keccakOut m.evm 0 32).1⟧) :=
    isOk_insert.mpr (by simp only [isOk_setEvm]; exact hmok)
  rw [Clear.evm_reviveJump_of_isOk hXok]
  simp only [evm_insert]
  rw [Clear.evm_setEvm_of_isOk hmok, Clear.StorageFrame.sload_keccakOut, hmdef,
    Clear.evm_setEvm_of_isOk hfok, Clear.StorageFrame.sload_mstore, hfdef,
    Clear.evm_initcall hok]

/-- **ACCOUNT FRAME.**  Same chain: hashing and a memory write leave the account map and
the execution environment alone. -/
lemma array_dataslot_array_bytes32_dyn_storage_ptr_account {data : Identifier}
    {ptr : Literal} {addr : Address} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_array_dataslot_array_bytes32_dyn_storage_ptr data ptr s₀ s₉) :
    Clear.EVMState.lookupAccount s₉.evm addr = Clear.EVMState.lookupAccount s₀.evm addr ∧
      s₉.evm.execution_env = s₀.evm.execution_env := by
  subst h
  set f := s₀☎️⟦["ptr"],[ptr]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := f🇪⟦Clear.EVMState.mstore f.evm 0 (f["ptr"]!!)⟧ with hmdef
  have hmok : isOk m := by rw [hmdef]; simp only [isOk_setEvm]; exact hfok
  simp only [Clear.KeccakPrimOps.primCall_keccakOut, multifill_cons, multifill_nil,
    evm_insert, evm_setStore]
  have hXok : isOk (m🇪⟦(Clear.KeccakDeterminism.keccakOut m.evm 0 32).2⟧⟦"data" ↦
      (Clear.KeccakDeterminism.keccakOut m.evm 0 32).1⟧) :=
    isOk_insert.mpr (by simp only [isOk_setEvm]; exact hmok)
  rw [Clear.evm_reviveJump_of_isOk hXok]
  simp only [evm_insert]
  rw [Clear.evm_setEvm_of_isOk hmok, Clear.StorageFrame.lookupAccount_keccakOut,
    Clear.StorageFrame.execution_env_keccakOut, hmdef, Clear.evm_setEvm_of_isOk hfok,
    Clear.StorageFrame.lookupAccount_mstore, Clear.StorageFrame.execution_env_mstore,
    hfdef, Clear.evm_initcall hok]
  exact ⟨rfl, rfl⟩

/-- **WHERE THE ELEMENTS START.**  The returned data slot is `keccak(ptr)` — over the
CALLER's argument and `s₀`'s own evm.  This is the companion of the index accessor's
`_val`: that one says where element `i` is, this one says where element `0` is, and the
copy loop writes at `dstSlot + i` off exactly this base. -/
lemma array_dataslot_array_bytes32_dyn_storage_ptr_val {data : Identifier} {ptr : Literal}
    {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_array_dataslot_array_bytes32_dyn_storage_ptr data ptr s₀ s₉) :
    s₉[data]!! = (Clear.KeccakDeterminism.keccakOut
      (Clear.EVMState.mstore s₀.evm 0 ptr) 0 32).1 := by
  subst h
  set f := s₀☎️⟦["ptr"],[ptr]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := f🇪⟦Clear.EVMState.mstore f.evm 0 (f["ptr"]!!)⟧ with hmdef
  have hmok : isOk m := by rw [hmdef]; simp only [isOk_setEvm]; exact hfok
  simp only [Clear.KeccakPrimOps.primCall_keccakOut, multifill_cons, multifill_nil]
  have hXok : isOk (m🇪⟦(Clear.KeccakDeterminism.keccakOut m.evm 0 32).2⟧⟦"data" ↦
      (Clear.KeccakDeterminism.keccakOut m.evm 0 32).1⟧) :=
    isOk_insert.mpr (by simp only [isOk_setEvm]; exact hmok)
  rw [lookup_insert' (isOk_setStore_of_isOk (by
      rw [revive_of_ok hXok]; exact hXok)),
    lookup_insert' (by simp only [isOk_setEvm]; exact hmok),
    hmdef, Clear.evm_setEvm_of_isOk hfok, hfdef, Clear.evm_initcall hok,
    Clear.lookup_initcall_one hok]

/-- **CONFIG FRAME.**  The data-slot helper's `mstore` and hash leave the keccak window
intact.  This is what lets a caller keep the low-slot separation hypotheses alive across
the call -- and, unlike the storage frame, it is what the NEXT hash in a chain needs, since
a keccak result depends on the whole evm rather than on any one slot. -/
lemma array_dataslot_array_bytes32_dyn_storage_ptr_config {data : Identifier}
    {ptr : Literal} {s₀ s₉ : State} (hok : isOk s₀)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_array_dataslot_array_bytes32_dyn_storage_ptr data ptr s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  subst h
  set f := s₀☎️⟦["ptr"],[ptr]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set m := f🇪⟦Clear.EVMState.mstore f.evm 0 (f["ptr"]!!)⟧ with hmdef
  have hmok : isOk m := by rw [hmdef]; simp only [isOk_setEvm]; exact hfok
  have hme : m.evm = Clear.EVMState.mstore s₀.evm 0 (f["ptr"]!!) := by
    rw [hmdef, Clear.evm_setEvm_of_isOk hfok, hfdef, Clear.evm_initcall hok]
  simp only [Clear.KeccakPrimOps.primCall_keccakOut, multifill_cons, multifill_nil,
    evm_insert, evm_setStore]
  have hXok : isOk (m🇪⟦(Clear.KeccakDeterminism.keccakOut m.evm 0 32).2⟧⟦"data" ↦
      (Clear.KeccakDeterminism.keccakOut m.evm 0 32).1⟧) :=
    isOk_insert.mpr (by simp only [isOk_setEvm]; exact hmok)
  rw [Clear.evm_reviveJump_of_isOk hXok]
  simp only [evm_insert]
  rw [Clear.evm_setEvm_of_isOk hmok]
  have hRm : Clear.KeccakLowSlot.RangeInWindow m.evm := by
    rw [hme]; exact Clear.StorageFrame.rangeInWindow_mstore hR
  have hCm : Clear.KeccakLowSlot.CachedInWindow m.evm := by
    rw [hme]; exact Clear.StorageFrame.cachedInWindow_mstore hC
  exact ⟨Clear.KeccakLowSlot.rangeInWindow_keccakOut hRm,
    Clear.KeccakLowSlot.cachedInWindow_keccakOut hRm hCm⟩

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
