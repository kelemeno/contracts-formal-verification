import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_4496777052991139710_gen


namespace L2InteropCommitmentTree.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def ACond_for_4496777052991139710 (s₀ : State) : Literal := fromBool (s₀["start"]!! < s₀["_1"]!!)
def APost_for_4496777052991139710 (s₀ s₉ : State) : Prop := True
def ABody_for_4496777052991139710 (s₀ s₉ : State) : Prop := True
def AFor_for_4496777052991139710 (s₀ s₉ : State) : Prop := True

lemma for_4496777052991139710_cond_abs_of_code {s₀ fuel} : eval fuel for_4496777052991139710_cond (s₀) = (s₀, ACond_for_4496777052991139710 (s₀)) := by
  unfold eval ACond_for_4496777052991139710
  simp [for_4496777052991139710_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_4496777052991139710_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_4496777052991139710_post_concrete_of_code s₀ s₉ →
  Spec APost_for_4496777052991139710 s₀ s₉ := by
  unfold APost_for_4496777052991139710
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

lemma for_4496777052991139710_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_4496777052991139710_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_4496777052991139710 s₀ s₉ := by
  unfold ABody_for_4496777052991139710
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

lemma AZero_for_4496777052991139710 : ∀ s₀, isOk s₀ → ACond_for_4496777052991139710 (👌 s₀) = 0 → AFor_for_4496777052991139710 s₀ s₀ := by
  intro s₀ _ _
  trivial
lemma AOk_for_4496777052991139710 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_4496777052991139710 s₀ = 0 → ABody_for_4496777052991139710 s₀ s₂ → APost_for_4496777052991139710 s₂ s₄ → Spec AFor_for_4496777052991139710 s₄ s₅ → AFor_for_4496777052991139710 s₀ s₅
:= by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _ _
  trivial
lemma AContinue_for_4496777052991139710 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_4496777052991139710 s₀ = 0 → ABody_for_4496777052991139710 s₀ s₂ → Spec APost_for_4496777052991139710 (🧟s₂) s₄ → Spec AFor_for_4496777052991139710 s₄ s₅ → AFor_for_4496777052991139710 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _
  trivial
lemma ABreak_for_4496777052991139710 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_4496777052991139710 s₀ = 0 → ABody_for_4496777052991139710 s₀ s₂ → AFor_for_4496777052991139710 s₀ (🧟s₂) := by
  intro s₀ s₂ _ _ _ _
  trivial
lemma ALeave_for_4496777052991139710 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_4496777052991139710 s₀ = 0 → ABody_for_4496777052991139710 s₀ s₂ → AFor_for_4496777052991139710 s₀ s₂ := by
  intro s₀ s₂ _ _ _ _
  trivial

end

end L2InteropCommitmentTree.Common
