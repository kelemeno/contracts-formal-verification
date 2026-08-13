import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_2003501192971474853_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The even-index sibling: neighbour, or the level's empty default.**

```
    switch eq(var_maxNodeNumber, var_index)
    case 0 { … sibling := level_i[var_index + 1] … }      -- an actual neighbour
    default { … sibling := defaults[var_i] … }            -- array at slot 3
```

An even-indexed node is a LEFT child, so its sibling is the node to its right — but
at the right edge of the level (`var_index == var_maxNodeNumber`) there is no such
node, and the tree uses the precomputed empty-subtree hash for that level, held in
the array at slot 3.  This is the deployed form of the rule
`AttackVectors/LastBatchInRoot.lean` reasons about abstractly.

Note how the generator encodes a `switch`: BOTH branch chains are asserted, and an
`ite` picks which result becomes the output.  So the spec carries both executions
even though only one is taken -- mirror that rather than trying to state only the
taken branch. -/
def A_switch_2003501192971474853 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_storage_array_index_access_bytes32_dyn_ptr "_9" "_10" 2 (s₀["var_i"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_checked_add_uint256 "split_expr_9" (s₁["var_index"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec (A_storage_array_index_access_bytes32_dyn_ptr "_11" "_12" (s₂["_9"]!!) (s₂["split_expr_9"]!!)) s₂ s₃ ∧
        (let ld := s₃⟦"split_expr_10" ↦ Clear.EVMState.sload s₃.evm (s₃["_11"]!!)⟧
         ∃ s₄, Spec (A_extract_from_storage_value_dynamict_bytes32 "expr" (ld["split_expr_10"]!!) (ld["_12"]!!)) ld s₄ ∧
           ∃ s₅, Spec (A_storage_array_index_access_bytes32_dyn_ptr "_13" "_14" 3 (s₀["var_i"]!!)) s₀ s₅ ∧
             (let ld2 := s₅⟦"split_expr_11" ↦ Clear.EVMState.sload s₅.evm (s₅["_13"]!!)⟧
              ∃ s₆, Spec (A_extract_from_storage_value_dynamict_bytes32 "expr" (ld2["split_expr_11"]!!) (ld2["_14"]!!)) ld2 s₆ ∧
                ((s₀["var_maxNodeNumber"]!! = s₀["var_index"]!! → s₉ = s₆) ∧
                 (s₀["var_maxNodeNumber"]!! ≠ s₀["var_index"]!! → s₉ = s₄))))

lemma switch_2003501192971474853_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_2003501192971474853_concrete_of_code s₀ s₉ →
  Spec A_switch_2003501192971474853 s₀ s₉ := by
  unfold switch_2003501192971474853_concrete_of_code A_switch_2003501192971474853
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, heq⟩ := hc
  -- stating the selection as two implications rather than mirroring the nested `ite`:
  -- the emitted ite carries a Decidable instance that does not unify with a hand-written
  -- one, and the two types then print identically while failing to typecheck
  refine ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, ?_, ?_⟩
  · intro hedge
    rw [← heq]
    simp [hedge]
  · intro hne
    rw [← heq]
    simp [hne]

/-- **Which sibling is used.**  At the right edge of the level the empty default is
taken; otherwise the neighbour at `index + 1`.  This falls straight out of the spec
now that the selection is stated as implications. -/
lemma switch_2003501192971474853_uses_default {s₀ s₉ : State} (h : A_switch_2003501192971474853 s₀ s₉)
    (hedge : s₀["var_maxNodeNumber"]!! = s₀["var_index"]!!) :
    ∃ s₅, Spec (A_storage_array_index_access_bytes32_dyn_ptr "_13" "_14" 3 (s₀["var_i"]!!)) s₀ s₅ := by
  obtain ⟨s₁, _, s₂, _, s₃, _, s₄, _, s₅, h₅, s₆, _, _, _⟩ := h
  exact ⟨s₅, h₅⟩

end

end L2InteropCommitmentTree.Common
