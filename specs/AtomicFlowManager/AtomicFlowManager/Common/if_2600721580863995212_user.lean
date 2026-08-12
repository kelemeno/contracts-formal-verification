import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x32

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2600721580863995212_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- The array-bounds guard, as a DICHOTOMY on the flag rather than an alias to its
concrete spec:

    if iszero(split_expr_1) { panic_error_0x32() }

`split_expr_1` is `lt(index, length)`, so a ZERO flag means the index is out of bounds
and control goes to `panic_error_0x32`; a nonzero flag leaves the state untouched.

Stating it this way is what lets callers conclude anything about the guard's output —
with the alias form they get an opaque blob, which is why the loops composing through
this could not close their `ABreak`. -/
def A_if_2600721580863995212 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_1"]!! ≠ 0 → s₉ = s₀) ∧
  (s₀["split_expr_1"]!! = 0 → ∃ s, Spec A_panic_error_0x32 s₀ s ∧ s₉ = s)

lemma if_2600721580863995212_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2600721580863995212_concrete_of_code s₀ s₉ →
  Spec A_if_2600721580863995212 s₀ s₉ := by
  unfold if_2600721580863995212_concrete_of_code A_if_2600721580863995212
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
