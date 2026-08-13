import Clear.ReasoningPrinciple
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

end

end L2InteropCommitmentTree.Common
