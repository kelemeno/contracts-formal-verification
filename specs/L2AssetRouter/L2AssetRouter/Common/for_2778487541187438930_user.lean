import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_8949096056776948580
import generated.L2AssetRouter.L2AssetRouter.Common.block_8996179040297561355
import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes

import generated.L2AssetRouter.L2AssetRouter.Common.for_2778487541187438930_gen


namespace L2AssetRouter.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def ACond_for_2778487541187438930 (s₀ : State) : Literal := fromBool (s₀["i"]!! < s₀["length"]!!)
def APost_for_2778487541187438930 (s₀ s₉ : State) : Prop := for_2778487541187438930_post_concrete_of_code.1 s₀ s₉
def ABody_for_2778487541187438930 (s₀ s₉ : State) : Prop := for_2778487541187438930_body_concrete_of_code.1 s₀ s₉
def AFor_for_2778487541187438930 (s₀ s₉ : State) : Prop := True

lemma for_2778487541187438930_cond_abs_of_code {s₀ fuel} : eval fuel for_2778487541187438930_cond (s₀) = (s₀, ACond_for_2778487541187438930 (s₀)) := by
  unfold eval ACond_for_2778487541187438930
  simp [for_2778487541187438930_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_2778487541187438930_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_2778487541187438930_post_concrete_of_code s₀ s₉ →
  Spec APost_for_2778487541187438930 s₀ s₉ := by
  intro h
  simpa [APost_for_2778487541187438930] using h

lemma for_2778487541187438930_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_2778487541187438930_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_2778487541187438930 s₀ s₉ := by
  intro h
  simpa [ABody_for_2778487541187438930] using h

lemma AZero_for_2778487541187438930 : ∀ s₀, isOk s₀ → ACond_for_2778487541187438930 (👌 s₀) = 0 → AFor_for_2778487541187438930 s₀ s₀ := by
  intro s₀ _ _
  trivial
lemma AOk_for_2778487541187438930 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_2778487541187438930 s₀ = 0 → ABody_for_2778487541187438930 s₀ s₂ → APost_for_2778487541187438930 s₂ s₄ → Spec AFor_for_2778487541187438930 s₄ s₅ → AFor_for_2778487541187438930 s₀ s₅
:= by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _ _
  trivial
lemma AContinue_for_2778487541187438930 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_2778487541187438930 s₀ = 0 → ABody_for_2778487541187438930 s₀ s₂ → Spec APost_for_2778487541187438930 (🧟s₂) s₄ → Spec AFor_for_2778487541187438930 s₄ s₅ → AFor_for_2778487541187438930 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _
  trivial
lemma ABreak_for_2778487541187438930 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_2778487541187438930 s₀ = 0 → ABody_for_2778487541187438930 s₀ s₂ → AFor_for_2778487541187438930 s₀ (🧟s₂) := by
  intro s₀ s₂ _ _ _ _
  trivial
lemma ALeave_for_2778487541187438930 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_2778487541187438930 s₀ = 0 → ABody_for_2778487541187438930 s₀ s₂ → AFor_for_2778487541187438930 s₀ s₂ := by
  intro s₀ s₂ _ _ _ _
  trivial

end

end L2AssetRouter.Common
