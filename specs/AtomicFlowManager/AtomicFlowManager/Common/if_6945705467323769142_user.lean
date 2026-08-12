import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x32

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6945705467323769142_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- The calldata array-bounds guard, as a DICHOTOMY on the flag (cf. `if_2600721580863995212`,
the memory-array counterpart):

    if iszero(split_expr_0) { panic_error_0x32() }

`split_expr_0` is `lt(index, length)`, so a ZERO flag is an out-of-bounds index. -/
def A_if_6945705467323769142 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_0"]!! ≠ 0 → s₉ = s₀) ∧
  (s₀["split_expr_0"]!! = 0 → ∃ s, Spec A_panic_error_0x32 s₀ s ∧ s₉ = s)

lemma if_6945705467323769142_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6945705467323769142_concrete_of_code s₀ s₉ →
  Spec A_if_6945705467323769142 s₀ s₉ := by
  unfold if_6945705467323769142_concrete_of_code A_if_6945705467323769142
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hp, heq⟩ := hc
  constructor
  · intro hne
    rw [if_neg hne] at heq
    exact heq.symm
  · intro hz
    rw [if_pos hz] at heq
    exact ⟨s, hp, heq.symm⟩
end

end AtomicFlowManager.Common
