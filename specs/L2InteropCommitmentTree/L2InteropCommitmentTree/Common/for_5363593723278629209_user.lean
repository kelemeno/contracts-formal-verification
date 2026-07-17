import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_6078234115189856909
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mod_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_4762420646048873450
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_8439353917263816235
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7643149059429413085
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_5363593723278629209_gen


namespace L2InteropCommitmentTree.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def ACond_for_5363593723278629209 (s₀ : State) : Literal := sorry 
def APost_for_5363593723278629209 (s₀ s₉ : State) : Prop := sorry
def ABody_for_5363593723278629209 (s₀ s₉ : State) : Prop := sorry
def AFor_for_5363593723278629209 (s₀ s₉ : State) : Prop := sorry

lemma for_5363593723278629209_cond_abs_of_code {s₀ fuel} : eval fuel for_5363593723278629209_cond (s₀) = (s₀, ACond_for_5363593723278629209 (s₀)) := by
  unfold eval ACond_for_5363593723278629209
  sorry

lemma for_5363593723278629209_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_5363593723278629209_post_concrete_of_code s₀ s₉ →
  Spec APost_for_5363593723278629209 s₀ s₉ := by
  sorry

lemma for_5363593723278629209_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_5363593723278629209_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_5363593723278629209 s₀ s₉ := by
  sorry

lemma AZero_for_5363593723278629209 : ∀ s₀, isOk s₀ → ACond_for_5363593723278629209 (👌 s₀) = 0 → AFor_for_5363593723278629209 s₀ s₀ := sorry
lemma AOk_for_5363593723278629209 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_5363593723278629209 s₀ = 0 → ABody_for_5363593723278629209 s₀ s₂ → APost_for_5363593723278629209 s₂ s₄ → Spec AFor_for_5363593723278629209 s₄ s₅ → AFor_for_5363593723278629209 s₀ s₅
:= sorry
lemma AContinue_for_5363593723278629209 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_5363593723278629209 s₀ = 0 → ABody_for_5363593723278629209 s₀ s₂ → Spec APost_for_5363593723278629209 (🧟s₂) s₄ → Spec AFor_for_5363593723278629209 s₄ s₅ → AFor_for_5363593723278629209 s₀ s₅ := sorry
lemma ABreak_for_5363593723278629209 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_5363593723278629209 s₀ = 0 → ABody_for_5363593723278629209 s₀ s₂ → AFor_for_5363593723278629209 s₀ (🧟s₂) := sorry
lemma ALeave_for_5363593723278629209 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_5363593723278629209 s₀ = 0 → ABody_for_5363593723278629209 s₀ s₂ → AFor_for_5363593723278629209 s₀ s₂ := sorry

end

end L2InteropCommitmentTree.Common
