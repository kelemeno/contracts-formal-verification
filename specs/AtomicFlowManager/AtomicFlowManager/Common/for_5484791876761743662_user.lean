import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6283262372819999209
import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4720374723594237178
import generated.AtomicFlowManager.AtomicFlowManager.checked_sub_uint256
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6050018508198951540

import generated.AtomicFlowManager.AtomicFlowManager.Common.for_5484791876761743662_gen


namespace AtomicFlowManager.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def ACond_for_5484791876761743662 (s₀ : State) : Literal := sorry 
def APost_for_5484791876761743662 (s₀ s₉ : State) : Prop := sorry
def ABody_for_5484791876761743662 (s₀ s₉ : State) : Prop := sorry
def AFor_for_5484791876761743662 (s₀ s₉ : State) : Prop := sorry

lemma for_5484791876761743662_cond_abs_of_code {s₀ fuel} : eval fuel for_5484791876761743662_cond (s₀) = (s₀, ACond_for_5484791876761743662 (s₀)) := by
  unfold eval ACond_for_5484791876761743662
  sorry

lemma for_5484791876761743662_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_5484791876761743662_post_concrete_of_code s₀ s₉ →
  Spec APost_for_5484791876761743662 s₀ s₉ := by
  sorry

lemma for_5484791876761743662_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_5484791876761743662_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_5484791876761743662 s₀ s₉ := by
  sorry

lemma AZero_for_5484791876761743662 : ∀ s₀, isOk s₀ → ACond_for_5484791876761743662 (👌 s₀) = 0 → AFor_for_5484791876761743662 s₀ s₀ := sorry
lemma AOk_for_5484791876761743662 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_5484791876761743662 s₀ = 0 → ABody_for_5484791876761743662 s₀ s₂ → APost_for_5484791876761743662 s₂ s₄ → Spec AFor_for_5484791876761743662 s₄ s₅ → AFor_for_5484791876761743662 s₀ s₅
:= sorry
lemma AContinue_for_5484791876761743662 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_5484791876761743662 s₀ = 0 → ABody_for_5484791876761743662 s₀ s₂ → Spec APost_for_5484791876761743662 (🧟s₂) s₄ → Spec AFor_for_5484791876761743662 s₄ s₅ → AFor_for_5484791876761743662 s₀ s₅ := sorry
lemma ABreak_for_5484791876761743662 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_5484791876761743662 s₀ = 0 → ABody_for_5484791876761743662 s₀ s₂ → AFor_for_5484791876761743662 s₀ (🧟s₂) := sorry
lemma ALeave_for_5484791876761743662 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_5484791876761743662 s₀ = 0 → ABody_for_5484791876761743662 s₀ s₂ → AFor_for_5484791876761743662 s₀ s₂ := sorry

end

end AtomicFlowManager.Common
