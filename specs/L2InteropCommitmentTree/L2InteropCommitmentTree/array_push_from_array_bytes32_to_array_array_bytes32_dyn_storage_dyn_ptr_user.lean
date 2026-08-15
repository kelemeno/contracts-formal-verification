import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakLowSlot
import specs.KeccakClean
import specs.StateOk
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_user

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4590714779410500988
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_228369243124659344
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_3779316958150250372
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_dataslot_array_array_bytes32_dyn_storage_dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_6561856544793224737

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Append a new INNER array holding one element** — the array-of-arrays push.

This is how the tree gains a level: the outer array's length goes up by one, and the new
inner array is created with length 1 and its single element written.

```
    oldLen := sload(array); reject oldLen ≥ 2^64        -- if_4590714779410500988
    sstore(array, oldLen + 1)                           -- outer length++
    slot, offset := storage_array_index_access(array, oldLen)
    reject offset ≠ 0                                   -- if_228369243124659344
    oldLen_1 := sload(slot); sstore(slot, 1)            -- inner length := 1
    clear elements 1 .. oldLen_1 of the inner array     -- if_3779316958150250372
    dstSlot := array_dataslot(slot); copy 1 word from srcPtr
```

The `oldLen_1` read and the zero-fill are what make reuse safe: the slot may hold a
STALE longer array from a previous life, and truncating to length 1 without clearing
would leave those elements readable.  Element 0 is not cleared because it is about to be
overwritten by the copy. -/
def A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr (array value0 : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["array", "value0"],[array, value0]⟧
  let g := f⟦"oldLen" ↦ Clear.EVMState.sload f.evm (f["array"]!!)⟧
  let gc := g⟦"split_expr_0" ↦ (decide (g["oldLen"]!! < 18446744073709551616)).toUInt256⟧
  ∃ s₁, Spec L2InteropCommitmentTree.Common.A_if_4590714779410500988 gc s₁ ∧
    (let inc := s₁⟦"split_expr_1" ↦ s₁["oldLen"]!! + 1⟧
     let st := inc🇪⟦Clear.EVMState.sstore s₁.evm (inc["array"]!!) (inc["split_expr_1"]!!)⟧
     ∃ s₂, Spec (A_storage_array_index_access_bytes32_dyn_ptr "slot" "offset"
         (st["array"]!!) (st["oldLen"]!!)) st s₂ ∧
       ∃ s₃, Spec L2InteropCommitmentTree.Common.A_if_228369243124659344 s₂ s₃ ∧
         (let ld := s₃⟦"oldLen_1" ↦ Clear.EVMState.sload s₃.evm (s₃["slot"]!!)⟧
          -- the sstore takes the PRE-insert evm, as elsewhere in this generator
          let one := ld🇪⟦Clear.EVMState.sstore s₃.evm (ld["slot"]!!) 1⟧
          ∃ s₄, Spec L2InteropCommitmentTree.Common.A_if_3779316958150250372 one s₄ ∧
            (let src := s₄⟦"srcPtr" ↦ s₄["value0"]!!⟧
             ∃ s₅, Spec (A_array_dataslot_array_bytes32_dyn_storage_ptr "dstSlot"
                 (src["slot"]!!)) src s₅ ∧
               ∃ s₆, Spec L2InteropCommitmentTree.Common.AFor_for_6561856544793224737
                   (s₅⟦"i" ↦ 0⟧) s₆ ∧
                 s₉ = 🧟s₆🏪⟦s₀⟧)))

lemma array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_abs_of_concrete {s₀ s₉ : State} {array value0} :
  Spec (array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_concrete_of_code.1 array value0) s₀ s₉ →
  Spec (A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr array value0) s₀ s₉ := by
  unfold array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_concrete_of_code A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, heq.symm⟩

lemma array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_isOk {array value0 : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr array value0 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, _, s₂, _, s₃, _, s₄, _, s₅, _, s₆, _, heq⟩ := h
  subst heq
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_not_break {array value0 : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr array value0 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_isOk hnf h)

/-- **THE LEVELS PUSH IN NORMAL FORM.**

The array-of-arrays push opens with exactly the same three statements as the plain one --
read the length, check it against `2 ^ 64`, store `oldLen + 1`, then take the address of
element `oldLen` -- so it reuses `pushGc`/`pushInc`/`pushSt` rather than re-deriving them.
Everything after the accessor is what makes this the ARRAY-OF-ARRAYS case: the inner
array's length is set to 1, its stale tail is zeroed, and one word is copied in.

Off the panic path the guard vanishes and the whole tail runs from `pushSt`, which is
closed over `s₀`. -/
lemma arrArrPush_normal {array value0 : Literal} {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616)
    (h : A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr
      array value0 s₀ s₉) :
    ∃ s₂, Spec (A_storage_array_index_access_bytes32_dyn_ptr "slot" "offset"
        array (Clear.EVMState.sload s₀.evm array)) (pushSt s₀ array value0) s₂ ∧
      ∃ s₃, Spec L2InteropCommitmentTree.Common.A_if_228369243124659344 s₂ s₃ ∧
        (let ld := s₃⟦"oldLen_1" ↦ Clear.EVMState.sload s₃.evm (s₃["slot"]!!)⟧
         let one := ld🇪⟦Clear.EVMState.sstore s₃.evm (ld["slot"]!!) 1⟧
         ∃ s₄, Spec L2InteropCommitmentTree.Common.A_if_3779316958150250372 one s₄ ∧
           (let src := s₄⟦"srcPtr" ↦ s₄["value0"]!!⟧
            ∃ s₅, Spec (A_array_dataslot_array_bytes32_dyn_storage_ptr "dstSlot"
                (src["slot"]!!)) src s₅ ∧
              ∃ s₆, Spec L2InteropCommitmentTree.Common.AFor_for_6561856544793224737
                  (s₅⟦"i" ↦ 0⟧) s₆ ∧
                s₉ = 🧟s₆🏪⟦s₀⟧)) := by
  obtain ⟨s₁, h₁, hrest⟩ := h
  have hf : isOk (s₀☎️⟦["array", "value0"],[array, value0]⟧) := isOk_initcall_of_isOk hok
  have hgceq : ((s₀☎️⟦["array", "value0"],[array, value0]⟧)⟦"oldLen" ↦
        Clear.EVMState.sload (s₀☎️⟦["array", "value0"],[array, value0]⟧).evm
          ((s₀☎️⟦["array", "value0"],[array, value0]⟧)["array"]!!)⟧)⟦"split_expr_0" ↦
      (decide (((s₀☎️⟦["array", "value0"],[array, value0]⟧)⟦"oldLen" ↦
          Clear.EVMState.sload (s₀☎️⟦["array", "value0"],[array, value0]⟧).evm
            ((s₀☎️⟦["array", "value0"],[array, value0]⟧)["array"]!!)⟧)["oldLen"]!!
        < 18446744073709551616)).toUInt256⟧ = pushGc s₀ array value0 := by
    rw [Clear.evm_initcall hok, Clear.lookup_initcall_fst hok, lookup_insert' hf]
    rfl
  rw [hgceq] at h₁
  obtain ⟨s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, heq⟩ := hrest
  -- fuel travels backwards along the whole chain
  have h6nf : ¬ ❓ s₆ := by
    intro hoo
    apply hnf
    rw [heq]
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h5nf : ¬ ❓ s₅ := by
    intro hoo
    apply h6nf
    apply Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₆
    simpa only [isOutOfFuel_insert'] using hoo
  have h4nf : ¬ ❓ s₄ := by
    intro hoo
    apply h5nf
    apply Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅
    simpa only [isOutOfFuel_insert'] using hoo
  have h3nf : ¬ ❓ s₃ := by
    intro hoo
    apply h4nf
    apply Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄
    simpa only [isOutOfFuel_setEvm', isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := by
    intro hoo
    apply h2nf
    apply Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
    simpa only [isOutOfFuel_setEvm', isOutOfFuel_insert'] using hoo
  have hs1 : s₁ = pushGc s₀ array value0 :=
    L2InteropCommitmentTree.Common.if_4590714779410500988_id_of_ne (pushGc_flag hok hfits)
      (Spec_ok_unfold (isOk_pushGc hok) h1nf h₁)
  subst hs1
  have hsteq : ((pushGc s₀ array value0)⟦"split_expr_1" ↦
        (pushGc s₀ array value0)["oldLen"]!! + 1⟧)🇪⟦
      Clear.EVMState.sstore (pushGc s₀ array value0).evm
        (((pushGc s₀ array value0)⟦"split_expr_1" ↦
          (pushGc s₀ array value0)["oldLen"]!! + 1⟧)["array"]!!)
        (((pushGc s₀ array value0)⟦"split_expr_1" ↦
          (pushGc s₀ array value0)["oldLen"]!! + 1⟧)["split_expr_1"]!!)⟧
      = pushSt s₀ array value0 := by
    rw [pushGc_oldLen hok, pushGc_evm hok]
    show ((pushInc s₀ array value0)🇪⟦Clear.EVMState.sstore s₀.evm
      ((pushInc s₀ array value0)["array"]!!)
      ((pushInc s₀ array value0)["split_expr_1"]!!)⟧) = _
    rw [pushInc_array hok, pushInc_split1 hok]
    rfl
  rw [hsteq, pushSt_array hok, pushSt_oldLen hok] at h₂
  exact ⟨s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, heq⟩

/-- **CLEAN FLAG, BACKWARDS.**  The nested push, end to end.

Six steps, and the flag walks back through all of them: the element-copy loop (an iff, it
only moves words), `array_dataslot` (a hash), the truncation guard (a hash), the `sstore`
that sets the new length, the offset guard (an iff), the address computation (a hash), and
the length write.

Three of the six hash, so the result is one-way -- as it must be, since a clean input
cannot promise a hash will succeed. -/
lemma arrArrPush_clean {array value0 : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr
      array value0 s₀ s₉) :
    Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, heq⟩ := arrArrPush_normal hok hnf hfits h
  -- fuel first, outermost in
  have h6nf : ¬ ❓ s₆ := by
    intro hoo; apply hnf; rw [heq]
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h5nf : ¬ ❓ s₅ := fun hoo => h6nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₆
    (by simpa only [isOutOfFuel_insert'] using hoo))
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅
    (by simpa only [isOutOfFuel_insert'] using hoo))
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄
    (by simpa only [isOutOfFuel_setEvm', isOutOfFuel_insert'] using hoo))
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  -- then `Ok`, innermost out
  have hstok : isOk (pushSt s₀ array value0) := isOk_pushSt hok
  have hs2 : isOk s₂ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h2nf (Spec_ok_unfold hstok h2nf h₂)
  have hs3 : isOk s₃ := L2InteropCommitmentTree.Common.if_228369243124659344_isOk hs2
    (Spec_ok_unfold hs2 h3nf h₃)
  have honeok : isOk ((s₃⟦"oldLen_1" ↦ Clear.EVMState.sload s₃.evm (s₃["slot"]!!)⟧)🇪⟦
      Clear.EVMState.sstore s₃.evm
        ((s₃⟦"oldLen_1" ↦ Clear.EVMState.sload s₃.evm (s₃["slot"]!!)⟧)["slot"]!!) 1⟧) := by
    simp only [isOk_setEvm, isOk_insert]; exact hs3
  have a₄ := Spec_ok_unfold honeok h4nf h₄
  have hs4 : isOk s₄ := L2InteropCommitmentTree.Common.if_3779316958150250372_isOk honeok
    h4nf a₄
  have hsrcok : isOk (s₄⟦"srcPtr" ↦ s₄["value0"]!!⟧) := isOk_insert.mpr hs4
  have a₅ := Spec_ok_unfold hsrcok h5nf h₅
  have hs5 : isOk s₅ := array_dataslot_array_bytes32_dyn_storage_ptr_isOk h5nf a₅
  have a₆ := Spec_ok_unfold (isOk_insert.mpr hs5) h6nf h₆
  -- now the flag, from the end back to the start
  rw [heq, evm_setStore, Clear.evm_reviveJump_of_isOk a₆.2.1] at hclean
  have c5 : Clear.KeccakClean.Clean s₅.evm := by
    have := a₆.2.2.2.2.mp hclean
    simpa only [evm_insert] using this
  have c4 : Clear.KeccakClean.Clean s₄.evm := by
    have := array_dataslot_array_bytes32_dyn_storage_ptr_clean hsrcok c5 a₅
    simpa only [evm_insert] using this
  have c3 : Clear.KeccakClean.Clean s₃.evm := by
    have := L2InteropCommitmentTree.Common.if_3779316958150250372_clean honeok h4nf c4 a₄
    rw [Clear.evm_setEvm_of_isOk (isOk_insert.mpr hs3),
      Clear.KeccakClean.clean_sstore] at this
    exact this
  have c2 : Clear.KeccakClean.Clean s₂.evm :=
    (L2InteropCommitmentTree.Common.if_228369243124659344_clean hs2
      (Spec_ok_unfold hs2 h3nf h₃)).mp c3
  have cst := storage_array_index_access_bytes32_dyn_ptr_clean hstok h2nf c2
    (Spec_ok_unfold hstok h2nf h₂)
  rw [pushSt_evm hok, Clear.KeccakClean.clean_sstore] at cst
  exact cst

/-- **KECCAK WINDOW, WHOLE CALL.**  Same six steps as `arrArrPush_clean`, forwards. -/
lemma arrArrPush_config {array value0 : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr
      array value0 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, heq⟩ := arrArrPush_normal hok hnf hfits h
  have h6nf : ¬ ❓ s₆ := by
    intro hoo; apply hnf; rw [heq]
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h5nf : ¬ ❓ s₅ := fun hoo => h6nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₆
    (by simpa only [isOutOfFuel_insert'] using hoo))
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅
    (by simpa only [isOutOfFuel_insert'] using hoo))
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄
    (by simpa only [isOutOfFuel_setEvm', isOutOfFuel_insert'] using hoo))
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have hstok : isOk (pushSt s₀ array value0) := isOk_pushSt hok
  have hs2 : isOk s₂ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h2nf (Spec_ok_unfold hstok h2nf h₂)
  have hs3 : isOk s₃ := L2InteropCommitmentTree.Common.if_228369243124659344_isOk hs2
    (Spec_ok_unfold hs2 h3nf h₃)
  have honeok : isOk ((s₃⟦"oldLen_1" ↦ Clear.EVMState.sload s₃.evm (s₃["slot"]!!)⟧)🇪⟦
      Clear.EVMState.sstore s₃.evm
        ((s₃⟦"oldLen_1" ↦ Clear.EVMState.sload s₃.evm (s₃["slot"]!!)⟧)["slot"]!!) 1⟧) := by
    simp only [isOk_setEvm, isOk_insert]; exact hs3
  have a₄ := Spec_ok_unfold honeok h4nf h₄
  have hs4 : isOk s₄ :=
    L2InteropCommitmentTree.Common.if_3779316958150250372_isOk honeok h4nf a₄
  have hsrcok : isOk (s₄⟦"srcPtr" ↦ s₄["value0"]!!⟧) := isOk_insert.mpr hs4
  have a₅ := Spec_ok_unfold hsrcok h5nf h₅
  have hs5 : isOk s₅ := array_dataslot_array_bytes32_dyn_storage_ptr_isOk h5nf a₅
  have a₆ := Spec_ok_unfold (isOk_insert.mpr hs5) h6nf h₆
  -- forwards from the length write
  obtain ⟨hRs, hCs⟩ := pushSt_config (array := array) (value0 := value0) hok hR hC
  obtain ⟨hR2, hC2⟩ := storage_array_index_access_bytes32_dyn_ptr_config hstok h2nf hRs hCs
    (Spec_ok_unfold hstok h2nf h₂)
  obtain ⟨hR3, hC3⟩ := L2InteropCommitmentTree.Common.if_228369243124659344_config hs2 hR2 hC2
    (Spec_ok_unfold hs2 h3nf h₃)
  have hone : ((s₃⟦"oldLen_1" ↦ Clear.EVMState.sload s₃.evm (s₃["slot"]!!)⟧)🇪⟦
      Clear.EVMState.sstore s₃.evm
        ((s₃⟦"oldLen_1" ↦ Clear.EVMState.sload s₃.evm (s₃["slot"]!!)⟧)["slot"]!!) 1⟧).evm
      = Clear.EVMState.sstore s₃.evm
          ((s₃⟦"oldLen_1" ↦ Clear.EVMState.sload s₃.evm (s₃["slot"]!!)⟧)["slot"]!!) 1 :=
    Clear.evm_setEvm_of_isOk (isOk_insert.mpr hs3)
  obtain ⟨hR4, hC4⟩ := L2InteropCommitmentTree.Common.if_3779316958150250372_config honeok h4nf
    (by rw [hone]; exact Clear.StorageFrame.rangeInWindow_sstore hR3)
    (by rw [hone]; exact Clear.StorageFrame.cachedInWindow_sstore hC3) a₄
  obtain ⟨hR5, hC5⟩ := array_dataslot_array_bytes32_dyn_storage_ptr_config hsrcok
    (by simp only [evm_insert]; exact hR4) (by simp only [evm_insert]; exact hC4) a₅
  obtain ⟨hR6, hC6⟩ := a₆.2.2.2.1 ⟨by simp only [evm_insert]; exact hR5,
    by simp only [evm_insert]; exact hC5⟩
  rw [heq, evm_setStore, Clear.evm_reviveJump_of_isOk a₆.2.1]
  exact ⟨hR6, hC6⟩

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
