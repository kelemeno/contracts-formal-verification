import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4006823798342809328
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_8218475617004033221
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_3711784909988835814
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_294889826768454570
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_5765234204941653661_gen


namespace L2InteropCommitmentTree.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def ACond_for_5765234204941653661 (s₀ : State) : Literal := 1
def APost_for_5765234204941653661 (s₀ s₉ : State) : Prop := True
def ABody_for_5765234204941653661 (s₀ s₉ : State) : Prop := True
def AFor_for_5765234204941653661 (s₀ s₉ : State) : Prop := True

lemma for_5765234204941653661_cond_abs_of_code {s₀ fuel} : eval fuel for_5765234204941653661_cond (s₀) = (s₀, ACond_for_5765234204941653661 (s₀)) := by
  unfold eval ACond_for_5765234204941653661
  simp [for_5765234204941653661_cond, Lit']

lemma for_5765234204941653661_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_5765234204941653661_post_concrete_of_code s₀ s₉ →
  Spec APost_for_5765234204941653661 s₀ s₉ := by
  unfold APost_for_5765234204941653661
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

lemma for_5765234204941653661_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_5765234204941653661_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_5765234204941653661 s₀ s₉ := by
  unfold ABody_for_5765234204941653661
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

lemma AZero_for_5765234204941653661 : ∀ s₀, isOk s₀ → ACond_for_5765234204941653661 (👌 s₀) = 0 → AFor_for_5765234204941653661 s₀ s₀ := by
  intro s₀ _ _
  trivial
lemma AOk_for_5765234204941653661 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_5765234204941653661 s₀ = 0 → ABody_for_5765234204941653661 s₀ s₂ → APost_for_5765234204941653661 s₂ s₄ → Spec AFor_for_5765234204941653661 s₄ s₅ → AFor_for_5765234204941653661 s₀ s₅
:= by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _ _
  trivial
lemma AContinue_for_5765234204941653661 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_5765234204941653661 s₀ = 0 → ABody_for_5765234204941653661 s₀ s₂ → Spec APost_for_5765234204941653661 (🧟s₂) s₄ → Spec AFor_for_5765234204941653661 s₄ s₅ → AFor_for_5765234204941653661 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _
  trivial
lemma ABreak_for_5765234204941653661 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_5765234204941653661 s₀ = 0 → ABody_for_5765234204941653661 s₀ s₂ → AFor_for_5765234204941653661 s₀ (🧟s₂) := by
  intro s₀ s₂ _ _ _ _
  trivial
lemma ALeave_for_5765234204941653661 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_5765234204941653661 s₀ = 0 → ABody_for_5765234204941653661 s₀ s₂ → AFor_for_5765234204941653661 s₀ s₂ := by
  intro s₀ s₂ _ _ _ _
  trivial

end

end L2InteropCommitmentTree.Common
