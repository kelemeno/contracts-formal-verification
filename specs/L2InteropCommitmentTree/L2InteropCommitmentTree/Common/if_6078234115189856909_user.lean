import Clear.ReasoningPrinciple
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_6078234115189856909_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Break when the levels run out**, the root loop's copy of the level-bound exit:
`if iszero(split_expr_4) { break }`.

Same shape as `if_4006823798342809328` in the level-walk loop but on a different
local, so it is a separate function to solc and cannot be ported onto that spec. -/
def A_if_6078234115189856909 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_5"]!! = 0 → s₉ = 💔s₀) ∧
  (s₀["split_expr_5"]!! ≠ 0 → s₉ = s₀)

lemma if_6078234115189856909_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6078234115189856909_concrete_of_code s₀ s₉ →
  Spec A_if_6078234115189856909 s₀ s₉ := by
  unfold if_6078234115189856909_concrete_of_code A_if_6078234115189856909
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  dsimp only at hc
  constructor
  · intro hg
    rw [if_pos hg] at hc
    exact hc.symm
  · intro hg
    rw [if_neg hg] at hc
    exact hc.symm

lemma if_6078234115189856909_isOk_of_not_taken {s₀ s₉ : State} (hok : isOk s₀) (hg : s₀["split_expr_5"]!! ≠ 0)
    (h : A_if_6078234115189856909 s₀ s₉) : isOk s₉ := by
  rw [h.2 hg]; exact hok

end

end L2InteropCommitmentTree.Common
