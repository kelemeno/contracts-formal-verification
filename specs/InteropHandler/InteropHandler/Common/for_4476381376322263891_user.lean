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
/-- Loop body: the three blocks in sequence, each at its own CLOSED FORM rather than
at the opaque concrete spec —

  1. `block_2862394693737849679`  the nested-slot derivation's first half:
     `keccak(bundleHash ‖ 2)` bound to `dataSlot_1`, scratch re-primed with `(var_i, dataSlot_1)`
  2. `block_5612315614323394231`  `slot := keccak(0,64)` (the leaf slot), `sload(slot)`, `not(255)`
  3. `block_8179420195348823280`  `sstore(slot, or(and(sload, not 255), 1))`

so the body writes `CallStatus.Executed = 1` into the low byte of
`callStatus[var_bundleHash][var_i]`, preserving the slot's high bytes.

This is the COMPOSITION, not yet the net effect: it names the three steps in abstract
terms, which is what the `AFor` induction consumes.  Deriving the single storage-write
statement from these three closed forms is the next step. -/
def ABody_for_4476381376322263891 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec A_block_2862394693737849679 s₀ s₁ ∧
    ∃ s₂, Spec A_block_5612315614323394231 s₁ s₂ ∧
      ∃ s₃, Spec A_block_8179420195348823280 s₂ s₃ ∧ s₃ = s₉
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
  unfold for_4476381376322263891_body_concrete_of_code ABody_for_4476381376322263891
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc

lemma AZero_for_4476381376322263891 : ∀ s₀, isOk s₀ → ACond_for_4476381376322263891 (👌 s₀) = 0 → AFor_for_4476381376322263891 s₀ s₀ := sorry
lemma AOk_for_4476381376322263891 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_4476381376322263891 s₀ = 0 → ABody_for_4476381376322263891 s₀ s₂ → APost_for_4476381376322263891 s₂ s₄ → Spec AFor_for_4476381376322263891 s₄ s₅ → AFor_for_4476381376322263891 s₀ s₅
:= sorry
lemma AContinue_for_4476381376322263891 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_4476381376322263891 s₀ = 0 → ABody_for_4476381376322263891 s₀ s₂ → Spec APost_for_4476381376322263891 (🧟s₂) s₄ → Spec AFor_for_4476381376322263891 s₄ s₅ → AFor_for_4476381376322263891 s₀ s₅ := sorry
lemma ABreak_for_4476381376322263891 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_4476381376322263891 s₀ = 0 → ABody_for_4476381376322263891 s₀ s₂ → AFor_for_4476381376322263891 s₀ (🧟s₂) := sorry
lemma ALeave_for_4476381376322263891 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_4476381376322263891 s₀ = 0 → ABody_for_4476381376322263891 s₀ s₂ → AFor_for_4476381376322263891 s₀ s₂ := sorry

end

end InteropHandler.Common
