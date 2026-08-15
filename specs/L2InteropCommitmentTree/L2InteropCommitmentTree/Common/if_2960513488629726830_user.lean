import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakFuel
import specs.KeccakLowSlot
import specs.KeccakClean
import specs.StateOk
import specs.StorageFrame
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_uint256_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2960513488629726830_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The index bound check**: `if gt(var_index, var_maxNodeNumber) { revert }`.

Reverts with the named custom error `MerkleWrongIndex(uint256,uint256)` -- selector
`shl(224, 458764239) = 0x1b582fcf`, resolved against era-contracts -- carrying BOTH the
offending index and the bound it exceeded, encoded by `abi_encode_uint256_uint256` into
the 68-byte payload.

So a leaf update outside the tree's current width fails loudly and says by how much,
rather than writing to a slot derived from an out-of-range index. -/
def A_if_2960513488629726830 (s₀ s₉ : State) : Prop :=
  let sel := Fin.shiftLeft 458764239 224
  let sm := Clear.State.multifill ["split_expr_2"] [sel] s₀
  let m := Clear.State.multifill ["split_expr_2"] [sel]
    s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (sm["split_expr_2"]!!)⟧
  ∃ s, Spec (A_abi_encode_uint256_uint256 "split_expr_3"
      (m["var_index"]!!) (m["var_maxNodeNumber"]!!)) m s ∧
    (s₀["var_index"]!! ≤ s₀["var_maxNodeNumber"]!! → s₉ = s₀) ∧
    (¬ (s₀["var_index"]!! ≤ s₀["var_maxNodeNumber"]!!) →
      s₉ = s🇪⟦Clear.EVMState.evm_revert s.evm 0 (s["split_expr_3"]!!)⟧)

lemma if_2960513488629726830_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2960513488629726830_concrete_of_code s₀ s₉ →
  Spec A_if_2960513488629726830 s₀ s₉ := by
  unfold if_2960513488629726830_concrete_of_code A_if_2960513488629726830
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, he, heq⟩ := hc
  refine ⟨s, he, ?_, ?_⟩
  · intro hg
    rw [if_pos hg] at heq
    exact heq.symm
  · intro hg
    rw [if_neg hg] at heq
    exact heq.symm

/-- Output is `Ok` on both branches: the input state, or the encoder's output with the
revert flag set. -/
lemma if_2960513488629726830_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_2960513488629726830 s₀ s₉) : isOk s₉ := by
  obtain ⟨s, he, h₁, h₂⟩ := h
  by_cases hg : s₀["var_index"]!! ≤ s₀["var_maxNodeNumber"]!!
  · rw [h₁ hg]; exact hok
  · have hsnf : ¬ ❓ s := by
      intro hoo
      apply hnf
      rw [h₂ hg]
      simpa only [isOutOfFuel_setEvm'] using hoo
    -- isOk_multifill will not unify with a multifill under a setEvm whose scrutinee is
    -- abstract; destructuring the state first makes the whole term reduce
    have hmok : isOk (Clear.State.multifill ["split_expr_2"] [Fin.shiftLeft 458764239 224]
        s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 ((Clear.State.multifill ["split_expr_2"]
          [Fin.shiftLeft 458764239 224] s₀)["split_expr_2"]!!)⟧) := by
      rcases s₀ with ⟨evm, store⟩ | _ | _
      · simp [multifill_cons, multifill_nil, isOk_insert, isOk_setEvm]
      · exact absurd hok (by simp [isOk])
      · exact absurd hok (by simp [isOk])
    have hsok : isOk s :=
      abi_encode_uint256_uint256_isOk hsnf (Spec_ok_unfold hmok hsnf he)
    rw [h₂ hg]
    simp only [isOk_setEvm]
    exact hsok

lemma if_2960513488629726830_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_2960513488629726830 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_2960513488629726830_isOk hok hnf h)


/-- **IN BOUNDS: THE GUARD CHANGES NOTHING** (generic-slot copy).  Same fact as
`if_4451958921457272093_id_of_le`, and here the spec already states it as an implication. -/
lemma if_2960513488629726830_id_of_le {s₀ s₉ : State}
    (hle : s₀["var_index"]!! ≤ s₀["var_maxNodeNumber"]!!)
    (h : A_if_2960513488629726830 s₀ s₉) : s₉ = s₀ := by
  obtain ⟨_, _, hpos, _⟩ := h
  exact hpos hle

/-! The reverting branch runs the encoder from `m`, the caller's state with the selector
bound and written to memory.  PARSE: `multifill vars vals s🇪⟦σ⟧` is
`(multifill vars vals s)🇪⟦σ⟧` -- the multifill is INNERMOST and the memory write sits
outside it.  These two facts about `m` are stated once and reused by all three frames. -/

private def guardM (s₀ : State) : State :=
  (Clear.State.multifill ["split_expr_2"] [Fin.shiftLeft 458764239 224] s₀)🇪⟦
    Clear.EVMState.mstore s₀.evm 0
      ((Clear.State.multifill ["split_expr_2"] [Fin.shiftLeft 458764239 224]
        s₀)["split_expr_2"]!!)⟧

private lemma guardM_isOk {s₀ : State} (hok : isOk s₀) : isOk (guardM s₀) := by
  unfold guardM
  simp only [isOk_setEvm]
  exact isOk_multifill hok

private lemma guardM_evm {s₀ : State} (hok : isOk s₀) :
    (guardM s₀).evm = Clear.EVMState.mstore s₀.evm 0
      ((Clear.State.multifill ["split_expr_2"] [Fin.shiftLeft 458764239 224]
        s₀)["split_expr_2"]!!) :=
  Clear.evm_setEvm_of_isOk (isOk_multifill hok)

/-- **STORAGE FRAME.**  The entry guard either passes the state through or encodes
`MerkleWrongIndex(index, bound)` into memory and reverts.  Neither writes storage, so a
caller carrying a slot past the bounds check needs no case analysis on whether it fired. -/
lemma if_2960513488629726830_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉) (h : A_if_2960513488629726830 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨se, hse, hpos, hneg⟩ := h
  by_cases hc : s₀["var_index"]!! ≤ s₀["var_maxNodeNumber"]!!
  · rw [hpos hc]
  · have hsnf : ¬ ❓ se := by rw [hneg hc] at hnf; simpa only [isOutOfFuel_setEvm'] using hnf
    have hspec : A_abi_encode_uint256_uint256 "split_expr_3" _ _ (guardM s₀) se :=
      Spec_ok_unfold (guardM_isOk hok) hsnf hse
    have hsok : isOk se := abi_encode_uint256_uint256_isOk hsnf hspec
    rw [hneg hc, Clear.evm_setEvm_of_isOk hsok, Clear.StorageFrame.sload_evm_revert,
      abi_encode_uint256_uint256_sload (guardM_isOk hok) hspec, guardM_evm hok,
      Clear.StorageFrame.sload_mstore]

/-- **CONFIG FRAME.**  Same two branches: a memory write and a revert keep the window. -/
lemma if_2960513488629726830_config {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_if_2960513488629726830 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧
      Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨se, hse, hpos, hneg⟩ := h
  by_cases hc : s₀["var_index"]!! ≤ s₀["var_maxNodeNumber"]!!
  · rw [hpos hc]
    exact ⟨hR, hC⟩
  · have hsnf : ¬ ❓ se := by rw [hneg hc] at hnf; simpa only [isOutOfFuel_setEvm'] using hnf
    have hspec : A_abi_encode_uint256_uint256 "split_expr_3" _ _ (guardM s₀) se :=
      Spec_ok_unfold (guardM_isOk hok) hsnf hse
    have hsok : isOk se := abi_encode_uint256_uint256_isOk hsnf hspec
    obtain ⟨hRe, hCe⟩ := abi_encode_uint256_uint256_config (guardM_isOk hok)
      (by rw [guardM_evm hok]; exact Clear.StorageFrame.rangeInWindow_mstore hR)
      (by rw [guardM_evm hok]; exact Clear.StorageFrame.cachedInWindow_mstore hC) hspec
    rw [hneg hc, Clear.evm_setEvm_of_isOk hsok]
    exact ⟨Clear.StorageFrame.rangeInWindow_evm_revert hRe,
      Clear.StorageFrame.cachedInWindow_evm_revert hCe⟩

/-- **FUEL FRAME.**  Neither branch spends pool. -/
lemma if_2960513488629726830_fuel {k : ℕ} {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hf : Clear.KeccakFuel.Fuel s₀.evm k)
    (h : A_if_2960513488629726830 s₀ s₉) : Clear.KeccakFuel.Fuel s₉.evm k := by
  obtain ⟨se, hse, hpos, hneg⟩ := h
  by_cases hc : s₀["var_index"]!! ≤ s₀["var_maxNodeNumber"]!!
  · rw [hpos hc]; exact hf
  · have hsnf : ¬ ❓ se := by rw [hneg hc] at hnf; simpa only [isOutOfFuel_setEvm'] using hnf
    have hspec : A_abi_encode_uint256_uint256 "split_expr_3" _ _ (guardM s₀) se :=
      Spec_ok_unfold (guardM_isOk hok) hsnf hse
    have hsok : isOk se := abi_encode_uint256_uint256_isOk hsnf hspec
    have hfe : Clear.KeccakFuel.Fuel se.evm k :=
      abi_encode_uint256_uint256_fuel (guardM_isOk hok)
        (by rw [guardM_evm hok]; exact Clear.KeccakFuel.Fuel.mstore _ _ hf) hspec
    rw [hneg hc, Clear.evm_setEvm_of_isOk hsok]
    exact Clear.KeccakFuel.Fuel.evm_revert _ _ hfe

/-- **CLEAN FLAG.**  The index-bound guard: on the failing branch it encodes a revert
reason and reverts, and neither step hashes.  A revert is a flag rather than a rollback in
this model, so it carries the collision bit across like everything else. -/
lemma if_2960513488629726830_clean {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_2960513488629726830 s₀ s₉) :
    Clear.KeccakClean.Clean s₉.evm ↔ Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨se, hse, hpos, hneg⟩ := h
  by_cases hc : s₀["var_index"]!! ≤ s₀["var_maxNodeNumber"]!!
  · rw [hpos hc]
  · have hsnf : ¬ ❓ se := by rw [hneg hc] at hnf; simpa only [isOutOfFuel_setEvm'] using hnf
    have hspec : A_abi_encode_uint256_uint256 "split_expr_3" _ _ (guardM s₀) se :=
      Spec_ok_unfold (guardM_isOk hok) hsnf hse
    have hsok : isOk se := abi_encode_uint256_uint256_isOk hsnf hspec
    rw [hneg hc, Clear.evm_setEvm_of_isOk hsok, Clear.KeccakClean.clean_evm_revert,
      abi_encode_uint256_uint256_clean (guardM_isOk hok) hspec, guardM_evm hok,
      Clear.KeccakClean.clean_mstore]

/-- **FRAME.**  The index-bound guard leaves the caller's bindings alone apart from the two
scratch slots the revert reason is built in -- so `var_index` and `var_maxNodeNumber` cross
it and reach the fold. -/
lemma if_2960513488629726830_frame {v : Identifier} {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉) (hv2 : v ≠ "split_expr_2") (hv3 : v ≠ "split_expr_3")
    (h : A_if_2960513488629726830 s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  obtain ⟨se, hse, hpos, hneg⟩ := h
  by_cases hc : s₀["var_index"]!! ≤ s₀["var_maxNodeNumber"]!!
  · rw [hpos hc]
  · have hsnf : ¬ ❓ se := by rw [hneg hc] at hnf; simpa only [isOutOfFuel_setEvm'] using hnf
    have hspec : A_abi_encode_uint256_uint256 "split_expr_3" _ _ (guardM s₀) se :=
      Spec_ok_unfold (guardM_isOk hok) hsnf hse
    have hsok : isOk se := abi_encode_uint256_uint256_isOk hsnf hspec
    rw [hneg hc, Clear.lookup_setEvm hsok,
      abi_encode_uint256_uint256_frame (guardM_isOk hok) hsnf hv3 hspec]
    -- and `guardM` is the caller's state with one scratch binding and a memory write
    unfold guardM
    rw [Clear.lookup_setEvm (isOk_multifill hok), multifill_cons, multifill_nil,
      lookup_insert_of_ne hv2]

end

end L2InteropCommitmentTree.Common
