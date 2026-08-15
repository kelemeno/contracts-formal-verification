import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakFuel
import specs.KeccakLowSlot
import specs.KeccakClean
import specs.StateOk
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_uint256_uint256_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Two-word revert payload**: `tail := 68; mstore(4, value0); mstore(36, value1)`.

The layout of a custom error carrying two `uint256`s: a 4-byte selector already at
offset 0, then the two words at 4 and 36, for a total length of 68.  Used by
`if_2960513488629726830` to revert with `MerkleWrongIndex(index, maxNodeNumber)`. -/
def A_abi_encode_uint256_uint256 (tail : Identifier) (value0 value1 : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["value0", "value1"],[value0, value1]⟧
  let t := f⟦"tail" ↦ 68⟧
  let m1 := t🇪⟦Clear.EVMState.mstore t.evm 4 (t["value0"]!!)⟧
  let m2 := m1🇪⟦Clear.EVMState.mstore m1.evm 36 (m1["value1"]!!)⟧
  s₉ = 🧟m2🏪⟦s₀⟧⟦tail ↦ m2["tail"]!!⟧

lemma abi_encode_uint256_uint256_abs_of_concrete {s₀ s₉ : State} {tail value0 value1} :
  Spec (abi_encode_uint256_uint256_concrete_of_code.1 tail value0 value1) s₀ s₉ →
  Spec (A_abi_encode_uint256_uint256 tail value0 value1) s₀ s₉ := by
  unfold abi_encode_uint256_uint256_concrete_of_code A_abi_encode_uint256_uint256
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

lemma abi_encode_uint256_uint256_isOk {tail : Identifier} {value0 value1 : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_abi_encode_uint256_uint256 tail value0 value1 s₀ s₉) : isOk s₉ := by
  subst h
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma abi_encode_uint256_uint256_not_break {tail : Identifier} {value0 value1 : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_abi_encode_uint256_uint256 tail value0 value1 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (abi_encode_uint256_uint256_isOk hnf h)

/-- The encoder's evm: two `mstore`s over the caller's, and nothing else. -/
private lemma abi_encode_evm_shape {tail : Identifier} {value0 value1 : Literal}
    {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_abi_encode_uint256_uint256 tail value0 value1 s₀ s₉) :
    ∃ a b c d : UInt256, s₉.evm = Clear.EVMState.mstore
      (Clear.EVMState.mstore s₀.evm a b) c d := by
  subst h
  set f := s₀☎️⟦["value0", "value1"],[value0, value1]⟧ with hfdef
  have hfok : isOk f := by rw [hfdef]; exact isOk_initcall_of_isOk hok
  set t := f⟦"tail" ↦ (68 : UInt256)⟧ with htdef
  have htok : isOk t := by rw [htdef]; exact isOk_insert.mpr hfok
  set m1 := t🇪⟦Clear.EVMState.mstore t.evm 4 (t["value0"]!!)⟧ with hm1def
  have hm1ok : isOk m1 := by rw [hm1def]; simpa only [isOk_setEvm] using htok
  set m2 := m1🇪⟦Clear.EVMState.mstore m1.evm 36 (m1["value1"]!!)⟧ with hm2def
  have hm2ok : isOk m2 := by rw [hm2def]; simpa only [isOk_setEvm] using hm1ok
  refine ⟨4, t["value0"]!!, 36, m1["value1"]!!, ?_⟩
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hm2ok, hm2def, Clear.evm_setEvm_of_isOk hm1ok, hm1def,
    Clear.evm_setEvm_of_isOk htok, htdef]
  simp only [evm_insert]
  rw [hfdef, Clear.evm_initcall hok]

/-- **STORAGE FRAME.**  The encoder writes memory only. -/
lemma abi_encode_uint256_uint256_sload {tail : Identifier} {value0 value1 : Literal}
    {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_abi_encode_uint256_uint256 tail value0 value1 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨a, b, c, d, he⟩ := abi_encode_evm_shape hok h
  rw [he, Clear.StorageFrame.sload_mstore, Clear.StorageFrame.sload_mstore]

/-- **CONFIG FRAME.**  Memory writes leave the keccak window intact. -/
lemma abi_encode_uint256_uint256_config {tail : Identifier} {value0 value1 : Literal}
    {s₀ s₉ : State} (hok : isOk s₀)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_abi_encode_uint256_uint256 tail value0 value1 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧
      Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨a, b, c, d, he⟩ := abi_encode_evm_shape hok h
  rw [he]
  exact ⟨Clear.StorageFrame.rangeInWindow_mstore
      (Clear.StorageFrame.rangeInWindow_mstore hR),
    Clear.StorageFrame.cachedInWindow_mstore (Clear.StorageFrame.cachedInWindow_mstore hC)⟩

/-- **FUEL FRAME.**  And it spends no pool. -/
lemma abi_encode_uint256_uint256_fuel {tail : Identifier} {value0 value1 : Literal} {k : ℕ}
    {s₀ s₉ : State} (hok : isOk s₀)
    (hf : Clear.KeccakFuel.Fuel s₀.evm k)
    (h : A_abi_encode_uint256_uint256 tail value0 value1 s₀ s₉) :
    Clear.KeccakFuel.Fuel s₉.evm k := by
  obtain ⟨a, b, c, d, he⟩ := abi_encode_evm_shape hok h
  rw [he]
  exact Clear.KeccakFuel.Fuel.mstore c d (Clear.KeccakFuel.Fuel.mstore a b hf)

/-- **CLEAN FLAG.**  The encoder is two memory writes; it cannot touch the flag. -/
lemma abi_encode_uint256_uint256_clean {tail : Identifier} {value0 value1 : Literal}
    {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_abi_encode_uint256_uint256 tail value0 value1 s₀ s₉) :
    Clear.KeccakClean.Clean s₉.evm ↔ Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨a, b, c, d, he⟩ := abi_encode_evm_shape hok h
  rw [he, Clear.KeccakClean.clean_mstore, Clear.KeccakClean.clean_mstore]

/-- **FRAME.**  The encoder writes memory, and restores the caller's bindings apart from
`tail`. -/
lemma abi_encode_uint256_uint256_frame {tail : Identifier} {value0 value1 : Literal}
    {v : Identifier} {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hv : v ≠ tail)
    (h : A_abi_encode_uint256_uint256 tail value0 value1 s₀ s₉) :
    s₉[v]!! = s₀[v]!! := by
  unfold A_abi_encode_uint256_uint256 at h
  subst h
  have hrev : isOk (🧟 (((s₀☎️⟦["value0", "value1"],[value0, value1]⟧⟦"tail" ↦ 68⟧)🇪⟦
      Clear.EVMState.mstore (s₀☎️⟦["value0", "value1"],[value0, value1]⟧⟦"tail" ↦ 68⟧).evm 4
        ((s₀☎️⟦["value0", "value1"],[value0, value1]⟧⟦"tail" ↦ 68⟧)["value0"]!!)⟧)🇪⟦
      Clear.EVMState.mstore ((s₀☎️⟦["value0", "value1"],[value0, value1]⟧⟦"tail" ↦ 68⟧)🇪⟦
        Clear.EVMState.mstore (s₀☎️⟦["value0", "value1"],[value0, value1]⟧⟦"tail" ↦ 68⟧).evm 4
          ((s₀☎️⟦["value0", "value1"],[value0, value1]⟧⟦"tail" ↦ 68⟧)["value0"]!!)⟧).evm 36
        (((s₀☎️⟦["value0", "value1"],[value0, value1]⟧⟦"tail" ↦ 68⟧)🇪⟦
          Clear.EVMState.mstore
            (s₀☎️⟦["value0", "value1"],[value0, value1]⟧⟦"tail" ↦ 68⟧).evm 4
            ((s₀☎️⟦["value0", "value1"],[value0, value1]⟧⟦"tail" ↦ 68⟧)["value0"]!!)⟧)["value1"]!!)⟧)) := by
    apply Clear.isOk_reviveJump_of_not_isOutOfFuel
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  rw [lookup_insert_of_ne hv, Clear.lookup_setStore hrev hok]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
