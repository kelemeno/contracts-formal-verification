import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr_5303
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_2668411367195639563_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Write the leaf, and seed the fold.**

```
    _1 := add(var_self_slot, 2)                 -- the LEVELS array
    _2, _3 := storage_array_index_access_…_5278(_1)      -- element 0 = level 0's array
    _4, _5 := storage_array_index_access_…(_2, var_index) -- the leaf's slot
    update_storage_value_bytes32_to_bytes32(_4, _5, var_itemHash)
    var_currentHash := var_itemHash
```

Two facts about the generic tree's layout drop out: the LEVELS array is at
`var_self_slot + 2` (with the defaults at `+ 3`, per the sibling switch), and level 0
is the LEAF level -- element 0 of the levels array.

The leaf slot is reached through both bounds checks (levels non-empty, index within
level 0), the value written is the caller's `var_itemHash`, and the running hash the
fold starts from is that same value -- so the fold recomputes from the leaf just
written, not from anything else. -/
def A_block_2668411367195639563 (s₀ s₉ : State) : Prop :=
  let a := s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧
  ∃ s₁, Spec (A_storage_array_index_access_bytes32_dyn_ptr_5303 "_2" "_3" (a["_1"]!!)) a s₁ ∧
    ∃ s₂, Spec (A_storage_array_index_access_bytes32_dyn_ptr "_4" "_5" (s₁["_2"]!!) (s₁["var_index"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec (A_update_storage_value_bytes32_to_bytes32
          (s₂["_4"]!!) (s₂["_5"]!!) (s₂["var_itemHash"]!!)) s₂ s₃ ∧
        s₉ = s₃⟦"var_currentHash" ↦ s₃["var_itemHash"]!!⟧

lemma block_2668411367195639563_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2668411367195639563_concrete_of_code s₀ s₉ →
  Spec A_block_2668411367195639563 s₀ s₉ := by
  unfold block_2668411367195639563_concrete_of_code A_block_2668411367195639563
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

lemma block_2668411367195639563_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_2668411367195639563 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  rw [heq] at hnf ⊢
  have h3nf : ¬ ❓ s₃ := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hain : isOk (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧) := by simpa [isOk_insert] using hok
  have hs1 : isOk s₁ :=
    storage_array_index_access_bytes32_dyn_ptr_5303_isOk h1nf (Spec_ok_unfold hain h1nf h₁)
  have hs2 : isOk s₂ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h2nf (Spec_ok_unfold hs1 h2nf h₂)
  have hs3 : isOk s₃ :=
    update_storage_value_bytes32_to_bytes32_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  simpa [isOk_insert] using hs3

lemma block_2668411367195639563_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_2668411367195639563 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_2668411367195639563_isOk hok hnf h)


/-- **FRAME.**  The leaf write moves `_1`.._5` and `var_currentHash`; the index and the
bound cross it untouched, so the guard's fact reaches the fold. -/
lemma block_2668411367195639563_frame {v : Identifier} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hv : v ∉ (["_1", "_2", "_3", "_4", "_5", "var_currentHash"] : List Identifier))
    (h : A_block_2668411367195639563 s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
  obtain ⟨h1, h2, h3, h4, h5, hcur⟩ := hv
  obtain ⟨s₁, hs₁, s₂, hs₂, s₃, hs₃, heq⟩ := h
  rw [heq] at hnf ⊢
  have haok : isOk (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧) := isOk_insert.mpr hok
  have h3nf : ¬ ❓ s₃ := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel hs₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel hs₂ hoo)
  have hok1 : isOk s₁ :=
    storage_array_index_access_bytes32_dyn_ptr_5303_isOk h1nf (Spec_ok_unfold haok h1nf hs₁)
  have hok2 : isOk s₂ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h2nf (Spec_ok_unfold hok1 h2nf hs₂)
  rw [lookup_insert_of_ne hcur,
    update_storage_value_bytes32_to_bytes32_frame hok2 h3nf (Spec_ok_unfold hok2 h3nf hs₃),
    storage_array_index_access_bytes32_dyn_ptr_frame hok1 h2nf h4 h5
      (Spec_ok_unfold hok1 h2nf hs₂),
    storage_array_index_access_bytes32_dyn_ptr_5303_frame haok h1nf h2 h3
      (Spec_ok_unfold haok h1nf hs₁),
    lookup_insert_of_ne h1]

end

end L2InteropCommitmentTree.Common
