import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4006823798342809328
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_8218475617004033221
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7020639558537270069
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_294889826768454570
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_2693611967757691411_gen


namespace L2InteropCommitmentTree.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def ACond_for_2693611967757691411 (s₀ : State) : Literal := sorry 
def APost_for_2693611967757691411 (s₀ s₉ : State) : Prop := sorry
def ABody_for_2693611967757691411 (s₀ s₉ : State) : Prop := sorry
def AFor_for_2693611967757691411 (s₀ s₉ : State) : Prop := sorry

lemma for_2693611967757691411_cond_abs_of_code {s₀ fuel} : eval fuel for_2693611967757691411_cond (s₀) = (s₀, ACond_for_2693611967757691411 (s₀)) := by
  unfold eval ACond_for_2693611967757691411
  sorry

lemma for_2693611967757691411_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_2693611967757691411_post_concrete_of_code s₀ s₉ →
  Spec APost_for_2693611967757691411 s₀ s₉ := by
  sorry

lemma for_2693611967757691411_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_2693611967757691411_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_2693611967757691411 s₀ s₉ := by
  sorry

lemma AZero_for_2693611967757691411 : ∀ s₀, isOk s₀ → ACond_for_2693611967757691411 (👌 s₀) = 0 → AFor_for_2693611967757691411 s₀ s₀ := sorry
lemma AOk_for_2693611967757691411 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_2693611967757691411 s₀ = 0 → ABody_for_2693611967757691411 s₀ s₂ → APost_for_2693611967757691411 s₂ s₄ → Spec AFor_for_2693611967757691411 s₄ s₅ → AFor_for_2693611967757691411 s₀ s₅
:= sorry
lemma AContinue_for_2693611967757691411 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_2693611967757691411 s₀ = 0 → ABody_for_2693611967757691411 s₀ s₂ → Spec APost_for_2693611967757691411 (🧟s₂) s₄ → Spec AFor_for_2693611967757691411 s₄ s₅ → AFor_for_2693611967757691411 s₀ s₅ := sorry
lemma ABreak_for_2693611967757691411 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_2693611967757691411 s₀ = 0 → ABody_for_2693611967757691411 s₀ s₂ → AFor_for_2693611967757691411 s₀ (🧟s₂) := sorry
lemma ALeave_for_2693611967757691411 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_2693611967757691411 s₀ = 0 → ABody_for_2693611967757691411 s₀ s₂ → AFor_for_2693611967757691411 s₀ s₂ := sorry

end

end L2InteropCommitmentTree.Common
