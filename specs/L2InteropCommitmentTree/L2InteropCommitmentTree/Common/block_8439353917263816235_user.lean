import Clear.ReasoningPrinciple
import specs.StateOk
import specs.KeccakLowSlot
import specs.StorageFrame
import specs.KeccakFuel
import specs.KeccakInjective
import specs.FinBits

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_8439353917263816235_gen


namespace L2InteropCommitmentTree.Common

section

open Clear Clear.StorageFrame Clear.KeccakLowSlot EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Advance one level**: halve the index and the node count, then derive the slot of
the parent node.

```
    var_index         := checked_div_uint256(var_index)
    var_maxNodeNumber := checked_div_uint256(var_maxNodeNumber)
    split_expr_12     := checked_add_uint256(var_i)          -- next level
    _15, _16 := storage_array_index_access(2, split_expr_12) -- that level's array
    _17, _18 := storage_array_index_access(_15, var_index)   -- the node in it
```

Both the index and the count halve together, and the level index increments, so the
slot handed to the write block is the parent of the node just hashed.  The array at
slot 2 is a literal, so the level array cannot be redirected. -/
def A_block_8439353917263816235 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_checked_div_uint256 "var_index" (s₀["var_index"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_checked_div_uint256 "var_maxNodeNumber" (s₁["var_maxNodeNumber"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec (A_checked_add_uint256 "split_expr_14" (s₂["var_i"]!!)) s₂ s₃ ∧
        ∃ s₄, Spec (A_storage_array_index_access_bytes32_dyn_ptr "_16" "_17" (s₃["_1"]!!)
            (s₃["split_expr_14"]!!)) s₃ s₄ ∧
          ∃ s₅, Spec (A_storage_array_index_access_bytes32_dyn_ptr "_18" "_19"
              (s₄["_16"]!!) (s₄["var_index"]!!)) s₄ s₅ ∧
            s₉ = s₅

lemma block_8439353917263816235_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8439353917263816235_concrete_of_code s₀ s₉ →
  Spec A_block_8439353917263816235 s₀ s₉ := by
  unfold block_8439353917263816235_concrete_of_code A_block_8439353917263816235
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq.symm⟩

lemma block_8439353917263816235_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_8439353917263816235 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hnf ⊢
  have h4nf : ¬ ❓ s₄ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ := checked_div_uint256_isOk hok (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ := checked_div_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
  have hs3 : isOk s₃ := checked_add_uint256_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  have hs4 : isOk s₄ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h4nf (Spec_ok_unfold hs3 h4nf h₄)
  exact storage_array_index_access_bytes32_dyn_ptr_isOk hnf (Spec_ok_unfold hs4 hnf h₅)

lemma block_8439353917263816235_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_8439353917263816235 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_8439353917263816235_isOk hok hnf h)


/-- **One level up.**  The block's five calls leave `var_index` at `index >>> 1`.

This is the first VALUE-level statement about a whole block of the fold, and it is what
the frame lemmas buy: only the first call writes `var_index`, and the other four are shown
not to touch it (`var_maxNodeNumber`, `split_expr_12`, `_15`/`_16`, `_17`/`_18` are all
distinct from it).  Without frames each of those calls could, for all the spec said,
rewrite anything.

`hlt`-free on purpose: the accessor's bounds hypothesis is only needed for its slot VALUE,
not for its frame, so the parent-index step holds whenever the block completes at all. -/
lemma block_8439353917263816235_index {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_8439353917263816235 s₀ s₉) :
    s₉["var_index"]!! = Fin.shiftRight (s₀["var_index"]!!) 1 := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hnf ⊢
  have h4nf : ¬ ❓ s₄ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ := checked_div_uint256_isOk hok (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ := checked_div_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
  have hs3 : isOk s₃ := checked_add_uint256_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  have hs4 : isOk s₄ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h4nf (Spec_ok_unfold hs3 h4nf h₄)
  have e1 : s₁["var_index"]!! = Fin.shiftRight (s₀["var_index"]!!) 1 :=
    checked_div_uint256_val hok (Spec_ok_unfold hok h1nf h₁)
  have e2 : s₂["var_index"]!! = s₁["var_index"]!! :=
    checked_div_uint256_frame hs1 (by decide) (Spec_ok_unfold hs1 h2nf h₂)
  have e3 : s₃["var_index"]!! = s₂["var_index"]!! :=
    checked_add_uint256_frame hs2 h3nf (by decide) (Spec_ok_unfold hs2 h3nf h₃)
  have e4 : s₄["var_index"]!! = s₃["var_index"]!! :=
    storage_array_index_access_bytes32_dyn_ptr_frame hs3 h4nf (by decide) (by decide)
      (Spec_ok_unfold hs3 h4nf h₄)
  have e5 : s₅["var_index"]!! = s₄["var_index"]!! :=
    storage_array_index_access_bytes32_dyn_ptr_frame hs4 hnf (by decide) (by decide)
      (Spec_ok_unfold hs4 hnf h₅)
  rw [e5, e4, e3, e2, e1]

/-- **FRAME.**  The parent-advance block writes `var_index`, `var_maxNodeNumber`, the
level temporary and the two accessor pairs -- and nothing else.  `var_i` in particular
crosses it untouched, which is why the level counter can be tracked by `APost` alone. -/
lemma block_8439353917263816235_frame {v : Identifier} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hv : v ∉ (["var_index", "var_maxNodeNumber", "split_expr_14", "_16", "_17", "_18",
      "_19"] : List Identifier))
    (h : A_block_8439353917263816235 s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
  obtain ⟨hidx, hmax, h12, h15, h16, h17, h18⟩ := hv
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hnf ⊢
  have h4nf : ¬ ❓ s₄ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ := checked_div_uint256_isOk hok (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ := checked_div_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
  have hs3 : isOk s₃ := checked_add_uint256_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  have hs4 : isOk s₄ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h4nf (Spec_ok_unfold hs3 h4nf h₄)
  have e1 : s₁[v]!! = s₀[v]!! :=
    checked_div_uint256_frame hok hidx (Spec_ok_unfold hok h1nf h₁)
  have e2 : s₂[v]!! = s₁[v]!! :=
    checked_div_uint256_frame hs1 hmax (Spec_ok_unfold hs1 h2nf h₂)
  have e3 : s₃[v]!! = s₂[v]!! :=
    checked_add_uint256_frame hs2 h3nf h12 (Spec_ok_unfold hs2 h3nf h₃)
  have e4 : s₄[v]!! = s₃[v]!! :=
    storage_array_index_access_bytes32_dyn_ptr_frame hs3 h4nf h15 h16
      (Spec_ok_unfold hs3 h4nf h₄)
  have e5 : s₅[v]!! = s₄[v]!! :=
    storage_array_index_access_bytes32_dyn_ptr_frame hs4 hnf h17 h18
      (Spec_ok_unfold hs4 hnf h₅)
  rw [e5, e4, e3, e2, e1]


/-- **STORAGE FRAME.**  The parent-advance block halves indices and computes an address;
it writes no storage. -/
lemma block_8439353917263816235_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉) (h : A_block_8439353917263816235 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hnf ⊢
  have h4nf : ¬ ❓ s₄ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ := checked_div_uint256_isOk hok (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ := checked_div_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
  have hs3 : isOk s₃ := checked_add_uint256_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  have hs4 : isOk s₄ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h4nf (Spec_ok_unfold hs3 h4nf h₄)
  rw [storage_array_index_access_bytes32_dyn_ptr_sload hs4 hnf (Spec_ok_unfold hs4 hnf h₅),
    storage_array_index_access_bytes32_dyn_ptr_sload hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄),
    checked_add_uint256_sload hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃),
    checked_div_uint256_evm hs1 (Spec_ok_unfold hs1 h2nf h₂),
    checked_div_uint256_evm hok (Spec_ok_unfold hok h1nf h₁)]


/-- **CONFIG FRAME.**  Halving and two address computations; the window survives. -/
lemma block_8439353917263816235_config {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : RangeInWindow s₀.evm) (hC : CachedInWindow s₀.evm)
    (h : A_block_8439353917263816235 s₀ s₉) :
    RangeInWindow s₉.evm ∧ CachedInWindow s₉.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hnf ⊢
  have h4nf : ¬ ❓ s₄ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ := checked_div_uint256_isOk hok (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ := checked_div_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
  have hs3 : isOk s₃ := checked_add_uint256_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  have hs4 : isOk s₄ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h4nf (Spec_ok_unfold hs3 h4nf h₄)
  have e1 : s₁.evm = s₀.evm := checked_div_uint256_evm hok (Spec_ok_unfold hok h1nf h₁)
  have e2 : s₂.evm = s₁.evm := checked_div_uint256_evm hs1 (Spec_ok_unfold hs1 h2nf h₂)
  obtain ⟨hR3, hC3⟩ := checked_add_uint256_config hs2 h3nf
    (by rw [e2, e1]; exact hR) (by rw [e2, e1]; exact hC) (Spec_ok_unfold hs2 h3nf h₃)
  obtain ⟨hR4, hC4⟩ := storage_array_index_access_bytes32_dyn_ptr_config hs3 h4nf hR3 hC3
    (Spec_ok_unfold hs3 h4nf h₄)
  exact storage_array_index_access_bytes32_dyn_ptr_config hs4 hnf hR4 hC4
    (Spec_ok_unfold hs4 hnf h₅)

/-- **THE SLOT THIS BLOCK WRITES IS NEVER A LOW SLOT.**

`ABody_..._writes_one_slot` produces the written slot as a witness but says nothing about
WHICH slot it is; this supplies the only thing a caller needs about it -- that it is not one
of the tree's constant-numbered slots, so a fold step cannot disturb the leaf count, the
level count or the defaults pointer.

Note what is NOT required: the array-length invariant.  The slot comes from the SECOND of
two accessor calls, and the accessor computes its address on both branches, so
`_slot_not_low` applies without the bounds check.  What is required is the keccak
configuration carried to that second call -- window, fuel, and the index below `2 ^ 32` --
and the index bound survives the descent because halving cannot raise a value. -/
lemma block_8439353917263816235_slot_not_low {c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hf : Clear.KeccakFuel.Fuel s₀.evm 2)
    (hj : (s₀["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound)
    (hcl : c.val < Clear.KeccakInjective.lowSlotBound)
    (h : A_block_8439353917263816235 s₀ s₉) : s₉["_18"]!! ≠ c := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hnf ⊢
  have h4nf : ¬ ❓ s₄ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ := checked_div_uint256_isOk hok (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ := checked_div_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
  have hs3 : isOk s₃ := checked_add_uint256_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  have hs4 : isOk s₄ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h4nf (Spec_ok_unfold hs3 h4nf h₄)
  -- the two divisions pass the whole machine state through
  have e1 : s₁.evm = s₀.evm := checked_div_uint256_evm hok (Spec_ok_unfold hok h1nf h₁)
  have e2 : s₂.evm = s₁.evm := checked_div_uint256_evm hs1 (Spec_ok_unfold hs1 h2nf h₂)
  -- window and fuel, carried to the SECOND accessor call
  obtain ⟨hR3, hC3⟩ := checked_add_uint256_config hs2 h3nf
    (by rw [e2, e1]; exact hR) (by rw [e2, e1]; exact hC) (Spec_ok_unfold hs2 h3nf h₃)
  obtain ⟨hR4, hC4⟩ := storage_array_index_access_bytes32_dyn_ptr_config hs3 h4nf hR3 hC3
    (Spec_ok_unfold hs3 h4nf h₄)
  have hf3 : Clear.KeccakFuel.Fuel s₃.evm 2 :=
    checked_add_uint256_fuel hs2 h3nf (by rw [e2, e1]; exact hf) (Spec_ok_unfold hs2 h3nf h₃)
  have hf4 : Clear.KeccakFuel.Fuel s₄.evm 1 :=
    storage_array_index_access_bytes32_dyn_ptr_fuel hs3 h4nf hf3 (Spec_ok_unfold hs3 h4nf h₄)
  -- the index halves once and stays below the bound
  have ei1 : s₁["var_index"]!! = Fin.shiftRight (s₀["var_index"]!!) 1 :=
    checked_div_uint256_val hok (Spec_ok_unfold hok h1nf h₁)
  have ei2 : s₂["var_index"]!! = s₁["var_index"]!! :=
    checked_div_uint256_frame hs1 (by decide) (Spec_ok_unfold hs1 h2nf h₂)
  have ei3 : s₃["var_index"]!! = s₂["var_index"]!! :=
    checked_add_uint256_frame hs2 h3nf (by decide) (Spec_ok_unfold hs2 h3nf h₃)
  have ei4 : s₄["var_index"]!! = s₃["var_index"]!! :=
    storage_array_index_access_bytes32_dyn_ptr_frame hs3 h4nf (by decide) (by decide)
      (Spec_ok_unfold hs3 h4nf h₄)
  have hjb : (s₄["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound := by
    rw [ei4, ei3, ei2, ei1]
    exact Clear.FinBits.shiftRight_one_lt_of_lt hj
  exact storage_array_index_access_bytes32_dyn_ptr_slot_not_low hs4 hnf hR4 hC4 hf4 hjb hcl
    (Spec_ok_unfold hs4 hnf h₅)

/-- **FUEL FRAME.**  Two units: the parent-advance block makes two accessor calls, and the
two divisions and the checked addition cost nothing. -/
lemma block_8439353917263816235_fuel {k : ℕ} {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hfu : Clear.KeccakFuel.Fuel s₀.evm (k + 2))
    (h : A_block_8439353917263816235 s₀ s₉) : Clear.KeccakFuel.Fuel s₉.evm k := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hnf ⊢
  have h4nf : ¬ ❓ s₄ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ := checked_div_uint256_isOk hok (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ := checked_div_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
  have hs3 : isOk s₃ := checked_add_uint256_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  have hs4 : isOk s₄ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h4nf (Spec_ok_unfold hs3 h4nf h₄)
  have e1 : s₁.evm = s₀.evm := checked_div_uint256_evm hok (Spec_ok_unfold hok h1nf h₁)
  have e2 : s₂.evm = s₁.evm := checked_div_uint256_evm hs1 (Spec_ok_unfold hs1 h2nf h₂)
  have hfu3 : Clear.KeccakFuel.Fuel s₃.evm (k + 2) :=
    checked_add_uint256_fuel hs2 h3nf (by rw [e2, e1]; exact hfu) (Spec_ok_unfold hs2 h3nf h₃)
  have hfu4 : Clear.KeccakFuel.Fuel s₄.evm (k + 1) :=
    storage_array_index_access_bytes32_dyn_ptr_fuel hs3 h4nf hfu3 (Spec_ok_unfold hs3 h4nf h₄)
  exact storage_array_index_access_bytes32_dyn_ptr_fuel hs4 hnf hfu4
    (Spec_ok_unfold hs4 hnf h₅)

end

end L2InteropCommitmentTree.Common
