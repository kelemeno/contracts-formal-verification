import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_8272958829832772907
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1472160955646587424
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_931273478728845735
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation_7868
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bytes1
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_429288736313321338
import generated.AtomicFlowManager.AtomicFlowManager.validator_revert_bool
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4813441911979294393
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_address
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4849067319072493286
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6391882241667270779
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_9170628658314157403
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4385546429568148802
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bytes
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6737038436070656367

import generated.AtomicFlowManager.AtomicFlowManager.Common.for_3999166119823801437_gen


namespace AtomicFlowManager.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def ACond_for_3999166119823801437 (s₀ : State) : Literal := sorry 
def APost_for_3999166119823801437 (s₀ s₉ : State) : Prop := sorry
def ABody_for_3999166119823801437 (s₀ s₉ : State) : Prop := sorry
def AFor_for_3999166119823801437 (s₀ s₉ : State) : Prop := sorry

lemma for_3999166119823801437_cond_abs_of_code {s₀ fuel} : eval fuel for_3999166119823801437_cond (s₀) = (s₀, ACond_for_3999166119823801437 (s₀)) := by
  unfold eval ACond_for_3999166119823801437
  sorry

lemma for_3999166119823801437_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_3999166119823801437_post_concrete_of_code s₀ s₉ →
  Spec APost_for_3999166119823801437 s₀ s₉ := by
  sorry

lemma for_3999166119823801437_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_3999166119823801437_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_3999166119823801437 s₀ s₉ := by
  sorry

lemma AZero_for_3999166119823801437 : ∀ s₀, isOk s₀ → ACond_for_3999166119823801437 (👌 s₀) = 0 → AFor_for_3999166119823801437 s₀ s₀ := sorry
lemma AOk_for_3999166119823801437 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_3999166119823801437 s₀ = 0 → ABody_for_3999166119823801437 s₀ s₂ → APost_for_3999166119823801437 s₂ s₄ → Spec AFor_for_3999166119823801437 s₄ s₅ → AFor_for_3999166119823801437 s₀ s₅
:= sorry
lemma AContinue_for_3999166119823801437 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_3999166119823801437 s₀ = 0 → ABody_for_3999166119823801437 s₀ s₂ → Spec APost_for_3999166119823801437 (🧟s₂) s₄ → Spec AFor_for_3999166119823801437 s₄ s₅ → AFor_for_3999166119823801437 s₀ s₅ := sorry
lemma ABreak_for_3999166119823801437 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_3999166119823801437 s₀ = 0 → ABody_for_3999166119823801437 s₀ s₂ → AFor_for_3999166119823801437 s₀ (🧟s₂) := sorry
lemma ALeave_for_3999166119823801437 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_3999166119823801437 s₀ = 0 → ABody_for_3999166119823801437 s₀ s₂ → AFor_for_3999166119823801437 s₀ s₂ := sorry

end

end AtomicFlowManager.Common
