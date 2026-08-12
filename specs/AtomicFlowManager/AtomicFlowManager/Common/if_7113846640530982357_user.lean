import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x11

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_7113846640530982357_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- The SUBTRACTION-UNDERFLOW guard, as a dichotomy:

    if gt(diff_1, var_i) { panic_error_0x11() }

`diff_1` is `sub(var_i, var_left)`, so `diff_1 > var_i` can only happen if that
subtraction wrapped — i.e. `var_left > var_i`. Panic 0x11 is Solidity's arithmetic
overflow/underflow panic, which is what this encodes at the Yul level.

Note the sense: the SAFE branch is `diff_1 ≤ var_i`, and it leaves the state untouched. -/
def A_if_7113846640530982357 (s₀ s₉ : State) : Prop :=
  (s₀["diff_1"]!! ≤ s₀["var_i"]!! → s₉ = s₀) ∧
  (¬ (s₀["diff_1"]!! ≤ s₀["var_i"]!!) → ∃ s, Spec A_panic_error_0x11 s₀ s ∧ s₉ = s)

lemma if_7113846640530982357_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7113846640530982357_concrete_of_code s₀ s₉ →
  Spec A_if_7113846640530982357 s₀ s₉ := by
  unfold if_7113846640530982357_concrete_of_code A_if_7113846640530982357
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hp, heq⟩ := hc
  constructor
  · intro hle
    rw [if_pos hle] at heq
    exact heq.symm
  · intro hgt
    rw [if_neg hgt] at heq
    exact ⟨s, hp, heq.symm⟩
end

end AtomicFlowManager.Common
