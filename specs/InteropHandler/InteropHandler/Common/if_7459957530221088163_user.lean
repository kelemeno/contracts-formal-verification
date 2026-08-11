import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_7459957530221088163_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    if iszero(expr) {
      let split_expr_38 := shl(225, 425816235)   -- MessageNotIncluded selector
      mstore(0, split_expr_38)
      revert(0, 4)
    }

The inclusion gate.  When the decoded `_proveInclusion` answer is zero the block
REVERTS; otherwise it is a no-op.  Stated as the two implications rather than a
closed form for the taken branch, because the security content is the revert
itself — `fun_verifyBundle_user.not_included_reverts` is the same fact proved
directly over this AST.

Note the block was previously listed as blocked by the large-shift wall
(`shl(225, …)`).  It is not: the shift is carried through symbolically by
`EVMShl'` and never evaluated.  See the corrected gap-2 entry in `AGENTS.md`.

Self-contained: does not mention `if_7459957530221088163_concrete_of_code`.
-/
def A_if_7459957530221088163 (s₀ s₉ : State) : Prop :=
  (s₀["expr"]!! = 0 → s₉.evm.reverted = true)
    ∧ (s₀["expr"]!! ≠ 0 → s₉ = s₀)

lemma if_7459957530221088163_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7459957530221088163_concrete_of_code s₀ s₉ →
  Spec A_if_7459957530221088163 s₀ s₉ := by
  unfold if_7459957530221088163_concrete_of_code A_if_7459957530221088163
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  refine ⟨?_, ?_⟩
  · intro hz
    rw [if_pos hz] at hc
    rw [← hc]
    rfl
  · intro hnz
    rw [if_neg hnz] at hc
    exact hc.symm

end

end InteropHandler.Common
