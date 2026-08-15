import Clear.ReasoningPrinciple
import specs.KeccakFuel
import specs.StateOk
import specs.KeccakLowSlot
import specs.KeccakClean
import specs.StorageFrame

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_896716371604423710_gen


namespace L2InteropCommitmentTree.Common

section

open Clear Clear.StorageFrame Clear.KeccakLowSlot EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The hash step**: `var_currentHash := fun_efficientHash(split_expr_8, var_currentHash)`.

One level of the Merkle fold.  The sibling comes first and the running hash second,
which is the ODD-index case: at an odd index the node is the right child, so its
sibling is on the left.  (The even case passes them the other way round.) -/
def A_block_896716371604423710 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec (A_fun_efficientHash "var_currentHash" (s₀["split_expr_9"]!!) (s₀["var_currentHash"]!!)) s₀ s ∧ s₉ = s

lemma block_896716371604423710_abs_of_concrete {s₀ s₉ : State} :
  Spec block_896716371604423710_concrete_of_code s₀ s₉ →
  Spec A_block_896716371604423710 s₀ s₉ := by
  unfold block_896716371604423710_concrete_of_code A_block_896716371604423710
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hs, heq⟩ := hc
  exact ⟨s, hs, heq.symm⟩

lemma block_896716371604423710_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_896716371604423710 s₀ s₉) : isOk s₉ := by
  obtain ⟨s, hs, heq⟩ := h
  rw [heq] at hnf ⊢
  exact fun_efficientHash_isOk hok (Spec_ok_unfold hok hnf hs)

lemma block_896716371604423710_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_896716371604423710 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_896716371604423710_isOk hok hnf h)


/-- **FRAME.**  One hash into `var_currentHash`; nothing else moves. -/
lemma block_896716371604423710_frame {v : Identifier} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hv : v ≠ "var_currentHash")
    (h : A_block_896716371604423710 s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  obtain ⟨s, hs, heq⟩ := h
  rw [heq] at hnf ⊢
  exact fun_efficientHash_frame hok hnf hv (Spec_ok_unfold hok hnf hs)


/-- **STORAGE FRAME.**  One hash; storage untouched. -/
lemma block_896716371604423710_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉) (h : A_block_896716371604423710 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨s, hs, heq⟩ := h
  rw [heq] at hnf ⊢
  exact fun_efficientHash_sload hok (Spec_ok_unfold hok hnf hs)


/-- **CONFIG FRAME.**  One hash. -/
lemma block_896716371604423710_config {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : RangeInWindow s₀.evm) (hC : CachedInWindow s₀.evm)
    (h : A_block_896716371604423710 s₀ s₉) :
    RangeInWindow s₉.evm ∧ CachedInWindow s₉.evm := by
  obtain ⟨s, hs, heq⟩ := h
  rw [heq] at hnf ⊢
  exact fun_efficientHash_config hok hR hC (Spec_ok_unfold hok hnf hs)

/-- **FUEL FRAME.**  This block is one call to the deployed hash, so it costs one unit. -/
lemma block_896716371604423710_fuel {k : ℕ} {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hf : Clear.KeccakFuel.Fuel s₀.evm (k + 1))
    (h : A_block_896716371604423710 s₀ s₉) : Clear.KeccakFuel.Fuel s₉.evm k := by
  obtain ⟨s, hs, heq⟩ := h
  rw [heq] at hnf ⊢
  exact fun_efficientHash_fuel hok hf (Spec_ok_unfold hok hnf hs)

/-- **CLEAN FLAG, BACKWARDS.**  This block is the fold's hash and nothing else. -/
lemma block_896716371604423710_clean {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_block_896716371604423710 s₀ s₉) :
    Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s, hs, heq⟩ := h
  rw [heq] at hnf hclean
  exact fun_efficientHash_clean hok hclean (Spec_ok_unfold hok hnf hs)

end

end L2InteropCommitmentTree.Common
