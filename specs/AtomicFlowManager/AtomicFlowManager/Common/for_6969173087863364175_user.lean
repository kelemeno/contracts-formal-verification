import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8769300753995681550
import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3757574592558380617
import generated.AtomicFlowManager.AtomicFlowManager.cleanup_address
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6945630744096063339
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1468183008278861216
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_bytes
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_9097063384830582942
import generated.AtomicFlowManager.AtomicFlowManager.revert_forward
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6066731633345594937
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bool_fromMemory
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5390487839625046806
import generated.AtomicFlowManager.AtomicFlowManager.increment_uint256

import generated.AtomicFlowManager.AtomicFlowManager.Common.for_6969173087863364175_gen


namespace AtomicFlowManager.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def ACond_for_6969173087863364175 (s₀ : State) : Literal := sorry 
def APost_for_6969173087863364175 (s₀ s₉ : State) : Prop := sorry
def ABody_for_6969173087863364175 (s₀ s₉ : State) : Prop := sorry
def AFor_for_6969173087863364175 (s₀ s₉ : State) : Prop := sorry

lemma for_6969173087863364175_cond_abs_of_code {s₀ fuel} : eval fuel for_6969173087863364175_cond (s₀) = (s₀, ACond_for_6969173087863364175 (s₀)) := by
  unfold eval ACond_for_6969173087863364175
  sorry

lemma for_6969173087863364175_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_6969173087863364175_post_concrete_of_code s₀ s₉ →
  Spec APost_for_6969173087863364175 s₀ s₉ := by
  sorry

lemma for_6969173087863364175_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_6969173087863364175_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_6969173087863364175 s₀ s₉ := by
  sorry

lemma AZero_for_6969173087863364175 : ∀ s₀, isOk s₀ → ACond_for_6969173087863364175 (👌 s₀) = 0 → AFor_for_6969173087863364175 s₀ s₀ := sorry
lemma AOk_for_6969173087863364175 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_6969173087863364175 s₀ = 0 → ABody_for_6969173087863364175 s₀ s₂ → APost_for_6969173087863364175 s₂ s₄ → Spec AFor_for_6969173087863364175 s₄ s₅ → AFor_for_6969173087863364175 s₀ s₅
:= sorry
lemma AContinue_for_6969173087863364175 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_6969173087863364175 s₀ = 0 → ABody_for_6969173087863364175 s₀ s₂ → Spec APost_for_6969173087863364175 (🧟s₂) s₄ → Spec AFor_for_6969173087863364175 s₄ s₅ → AFor_for_6969173087863364175 s₀ s₅ := sorry
lemma ABreak_for_6969173087863364175 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_6969173087863364175 s₀ = 0 → ABody_for_6969173087863364175 s₀ s₂ → AFor_for_6969173087863364175 s₀ (🧟s₂) := sorry
lemma ALeave_for_6969173087863364175 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_6969173087863364175 s₀ = 0 → ABody_for_6969173087863364175 s₀ s₂ → AFor_for_6969173087863364175 s₀ s₂ := sorry

end

end AtomicFlowManager.Common
