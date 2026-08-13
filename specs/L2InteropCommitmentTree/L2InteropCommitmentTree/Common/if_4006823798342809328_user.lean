import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4006823798342809328_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Break when the levels run out**: `if iszero(split_expr_6) { break }`, where
`split_expr_6` is `lt(var_i, sload(0))` — the level index against the stored level
count.

This is one of the level-walk loop's two exits.  Unlike every guard closed so far it
yields a `Break` checkpoint, so there is no `isOk` lemma: the whole point of the
state it produces is that it is NOT `Ok`. -/
def A_if_4006823798342809328 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_6"]!! = 0 → s₉ = 💔s₀) ∧
  (s₀["split_expr_6"]!! ≠ 0 → s₉ = s₀)

lemma if_4006823798342809328_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4006823798342809328_concrete_of_code s₀ s₉ →
  Spec A_if_4006823798342809328 s₀ s₉ := by
  unfold if_4006823798342809328_concrete_of_code A_if_4006823798342809328
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

/-- On the non-breaking branch the state is untouched, so it is still `Ok`.  There is
no unconditional `isOk` here -- the breaking branch is a `Break` checkpoint by design. -/
lemma if_4006823798342809328_isOk_of_not_taken {s₀ s₉ : State} (hok : isOk s₀) (hg : s₀["split_expr_6"]!! ≠ 0)
    (h : A_if_4006823798342809328 s₀ s₉) : isOk s₉ := by
  rw [h.2 hg]; exact hok

end

end L2InteropCommitmentTree.Common
