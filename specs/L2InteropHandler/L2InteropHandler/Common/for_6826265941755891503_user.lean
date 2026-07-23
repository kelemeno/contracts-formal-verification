import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.for_6826265941755891503_gen


namespace L2InteropHandler.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def ACond_for_6826265941755891503 (s₀ : State) : Literal := fromBool (s₀["i"]!! < s₀["length_1"]!!)
def APost_for_6826265941755891503 (s₀ s₉ : State) : Prop := for_6826265941755891503_post_concrete_of_code.1 s₀ s₉
def ABody_for_6826265941755891503 (s₀ s₉ : State) : Prop := for_6826265941755891503_body_concrete_of_code.1 s₀ s₉
def AFor_for_6826265941755891503 (s₀ s₉ : State) : Prop := True

lemma for_6826265941755891503_cond_abs_of_code {s₀ fuel} : eval fuel for_6826265941755891503_cond (s₀) = (s₀, ACond_for_6826265941755891503 (s₀)) := by
  unfold eval ACond_for_6826265941755891503
  simp [for_6826265941755891503_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_6826265941755891503_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_6826265941755891503_post_concrete_of_code s₀ s₉ →
  Spec APost_for_6826265941755891503 s₀ s₉ := by
  intro h
  simpa [APost_for_6826265941755891503] using h

lemma for_6826265941755891503_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_6826265941755891503_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_6826265941755891503 s₀ s₉ := by
  intro h
  simpa [ABody_for_6826265941755891503] using h

lemma AZero_for_6826265941755891503 : ∀ s₀, isOk s₀ → ACond_for_6826265941755891503 (👌 s₀) = 0 → AFor_for_6826265941755891503 s₀ s₀ := by
  intro s₀ _ _
  trivial
lemma AOk_for_6826265941755891503 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_6826265941755891503 s₀ = 0 → ABody_for_6826265941755891503 s₀ s₂ → APost_for_6826265941755891503 s₂ s₄ → Spec AFor_for_6826265941755891503 s₄ s₅ → AFor_for_6826265941755891503 s₀ s₅
:= by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _ _
  trivial
lemma AContinue_for_6826265941755891503 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_6826265941755891503 s₀ = 0 → ABody_for_6826265941755891503 s₀ s₂ → Spec APost_for_6826265941755891503 (🧟s₂) s₄ → Spec AFor_for_6826265941755891503 s₄ s₅ → AFor_for_6826265941755891503 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _
  trivial
lemma ABreak_for_6826265941755891503 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_6826265941755891503 s₀ = 0 → ABody_for_6826265941755891503 s₀ s₂ → AFor_for_6826265941755891503 s₀ (🧟s₂) := by
  intro s₀ s₂ _ _ _ _
  trivial
lemma ALeave_for_6826265941755891503 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_6826265941755891503 s₀ = 0 → ABody_for_6826265941755891503 s₀ s₂ → AFor_for_6826265941755891503 s₀ s₂ := by
  intro s₀ s₂ _ _ _ _
  trivial

end

end L2InteropHandler.Common
