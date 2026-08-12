import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_2862394693737849679
import generated.InteropHandler.InteropHandler.Common.block_5612315614323394231
import generated.InteropHandler.InteropHandler.Common.block_8179420195348823280

import generated.InteropHandler.InteropHandler.Common.for_4476381376322263891_gen


namespace InteropHandler.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

/-- Loop condition: `lt(var_i, length)` — the per-call index has not reached the bundle's call count. -/
def ACond_for_4476381376322263891 (s₀ : State) : Literal :=
  fromBool (s₀["var_i"]!! < s₀["length"]!!)
/-- Loop post: `var_i := add(var_i, 1)` — the index advances by one and nothing else moves. -/
def APost_for_4476381376322263891 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"var_i" ↦ ((Ok evm store)["var_i"]!! + 1)⟧
def ABody_for_4476381376322263891 (s₀ s₉ : State) : Prop := sorry
def AFor_for_4476381376322263891 (s₀ s₉ : State) : Prop := sorry

lemma for_4476381376322263891_cond_abs_of_code {s₀ fuel} : eval fuel for_4476381376322263891_cond (s₀) = (s₀, ACond_for_4476381376322263891 (s₀)) := by
  unfold eval ACond_for_4476381376322263891
  simp [for_4476381376322263891_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_4476381376322263891_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_4476381376322263891_post_concrete_of_code s₀ s₉ →
  Spec APost_for_4476381376322263891 s₀ s₉ := by
  unfold for_4476381376322263891_post_concrete_of_code APost_for_4476381376322263891
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma for_4476381376322263891_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_4476381376322263891_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_4476381376322263891 s₀ s₉ := by
  sorry

lemma AZero_for_4476381376322263891 : ∀ s₀, isOk s₀ → ACond_for_4476381376322263891 (👌 s₀) = 0 → AFor_for_4476381376322263891 s₀ s₀ := sorry
lemma AOk_for_4476381376322263891 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_4476381376322263891 s₀ = 0 → ABody_for_4476381376322263891 s₀ s₂ → APost_for_4476381376322263891 s₂ s₄ → Spec AFor_for_4476381376322263891 s₄ s₅ → AFor_for_4476381376322263891 s₀ s₅
:= sorry
lemma AContinue_for_4476381376322263891 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_4476381376322263891 s₀ = 0 → ABody_for_4476381376322263891 s₀ s₂ → Spec APost_for_4476381376322263891 (🧟s₂) s₄ → Spec AFor_for_4476381376322263891 s₄ s₅ → AFor_for_4476381376322263891 s₀ s₅ := sorry
lemma ABreak_for_4476381376322263891 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_4476381376322263891 s₀ = 0 → ABody_for_4476381376322263891 s₀ s₂ → AFor_for_4476381376322263891 s₀ (🧟s₂) := sorry
lemma ALeave_for_4476381376322263891 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_4476381376322263891 s₀ = 0 → ABody_for_4476381376322263891 s₀ s₂ → AFor_for_4476381376322263891 s₀ s₂ := sorry

end

end InteropHandler.Common
