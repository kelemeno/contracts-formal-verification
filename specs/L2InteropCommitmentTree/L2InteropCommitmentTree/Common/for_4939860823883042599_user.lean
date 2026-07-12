import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2425414531525476249
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mod_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_7836749200582770074
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_2743596091140315824
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_2896862189596047701
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_4939860823883042599_gen


namespace L2InteropCommitmentTree.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def ACond_for_4939860823883042599 (s₀ : State) : Literal := 1
def APost_for_4939860823883042599 (s₀ s₉ : State) : Prop := True
def ABody_for_4939860823883042599 (s₀ s₉ : State) : Prop := True
def AFor_for_4939860823883042599 (s₀ s₉ : State) : Prop := True

lemma for_4939860823883042599_cond_abs_of_code {s₀ fuel} : eval fuel for_4939860823883042599_cond (s₀) = (s₀, ACond_for_4939860823883042599 (s₀)) := by
  unfold eval ACond_for_4939860823883042599
  simp [for_4939860823883042599_cond, Lit']

lemma for_4939860823883042599_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_4939860823883042599_post_concrete_of_code s₀ s₉ →
  Spec APost_for_4939860823883042599 s₀ s₉ := by
  unfold APost_for_4939860823883042599
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

lemma for_4939860823883042599_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_4939860823883042599_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_4939860823883042599 s₀ s₉ := by
  unfold ABody_for_4939860823883042599
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

lemma AZero_for_4939860823883042599 : ∀ s₀, isOk s₀ → ACond_for_4939860823883042599 (👌 s₀) = 0 → AFor_for_4939860823883042599 s₀ s₀ := by
  intro s₀ _ _
  trivial
lemma AOk_for_4939860823883042599 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_4939860823883042599 s₀ = 0 → ABody_for_4939860823883042599 s₀ s₂ → APost_for_4939860823883042599 s₂ s₄ → Spec AFor_for_4939860823883042599 s₄ s₅ → AFor_for_4939860823883042599 s₀ s₅
:= by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _ _
  trivial
lemma AContinue_for_4939860823883042599 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_4939860823883042599 s₀ = 0 → ABody_for_4939860823883042599 s₀ s₂ → Spec APost_for_4939860823883042599 (🧟s₂) s₄ → Spec AFor_for_4939860823883042599 s₄ s₅ → AFor_for_4939860823883042599 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _
  trivial
lemma ABreak_for_4939860823883042599 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_4939860823883042599 s₀ = 0 → ABody_for_4939860823883042599 s₀ s₂ → AFor_for_4939860823883042599 s₀ (🧟s₂) := by
  intro s₀ s₂ _ _ _ _
  trivial
lemma ALeave_for_4939860823883042599 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_4939860823883042599 s₀ = 0 → ABody_for_4939860823883042599 s₀ s₂ → AFor_for_4939860823883042599 s₀ s₂ := by
  intro s₀ s₂ _ _ _ _
  trivial

end

end L2InteropCommitmentTree.Common
