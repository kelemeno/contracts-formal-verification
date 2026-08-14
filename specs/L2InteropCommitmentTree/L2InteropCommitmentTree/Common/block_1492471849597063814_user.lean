import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn_5278
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1492471849597063814_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **WRITE THE LEAF.**  `self._nodes[0][_index] = _itemHash`, then seed the fold.

```
    _1, _2 := storage_array_index_access(2)          -- _nodes[0]'s slot (array inlined)
    _3, _4 := storage_array_index_access(_1, var_index)
    update_storage_value(_3, _4, var_itemHash)
    var_currentHash := var_itemHash ; var_i := 0
```

Between the index guard and the loop, so what matters here is the FRAME: the index and the
bound must reach the loop unchanged. -/
def A_block_1492471849597063814 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_storage_array_index_access_bytes32_dyn__dyn_5278 "_1" "_2" 2) s₀ s₁ ∧
    ∃ s₂, Spec (A_storage_array_index_access_bytes32_dyn__dyn "_3" "_4"
        (s₁["_1"]!!) (s₁["var_index"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec (A_update_storage_value_bytes32_to_bytes32
          (s₂["_3"]!!) (s₂["_4"]!!) (s₂["var_itemHash"]!!)) s₂ s₃ ∧
        s₉ = s₃⟦"var_currentHash" ↦ s₃["var_itemHash"]!!⟧⟦"var_i" ↦ 0⟧

lemma block_1492471849597063814_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1492471849597063814_concrete_of_code s₀ s₉ →
  Spec A_block_1492471849597063814 s₀ s₉ := by
  unfold block_1492471849597063814_concrete_of_code A_block_1492471849597063814
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

/-- **FRAME.**  The leaf write touches `_1`.._4`, `var_currentHash` and `var_i` -- so
`var_index` and `var_maxNodeNumber` cross it untouched and the guard's bound reaches the
loop. -/
lemma block_1492471849597063814_frame {v : Identifier} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hv : v ∉ (["_1", "_2", "_3", "_4", "var_currentHash", "var_i"] : List Identifier))
    (h : A_block_1492471849597063814 s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
  obtain ⟨h1, h2, h3, h4, hcur, hvi⟩ := hv
  obtain ⟨s₁, hs₁, s₂, hs₂, s₃, hs₃, heq⟩ := h
  rw [heq] at hnf ⊢
  have h3nf : ¬ ❓ s₃ := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel hs₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel hs₂ hoo)
  have hok1 : isOk s₁ :=
    storage_array_index_access_bytes32_dyn__dyn_5278_isOk h1nf (Spec_ok_unfold hok h1nf hs₁)
  have hok2 : isOk s₂ :=
    storage_array_index_access_bytes32_dyn__dyn_isOk h2nf (Spec_ok_unfold hok1 h2nf hs₂)
  rw [lookup_insert_of_ne hvi, lookup_insert_of_ne hcur,
    update_storage_value_bytes32_to_bytes32_frame hok2 h3nf (Spec_ok_unfold hok2 h3nf hs₃),
    storage_array_index_access_bytes32_dyn__dyn_frame hok1 h2nf h3 h4
      (Spec_ok_unfold hok1 h2nf hs₂),
    storage_array_index_access_bytes32_dyn__dyn_5278_frame hok h1nf h1 h2
      (Spec_ok_unfold hok h1nf hs₁)]
end

end L2InteropCommitmentTree.Common
