import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_932755155890173629
import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_uint256_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_uint256_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_253019513998627002
import generated.AtomicFlowManager.AtomicFlowManager.checked_sub_uint256
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6050018508198951540

import generated.AtomicFlowManager.AtomicFlowManager.Common.for_9042030553971780173_gen


namespace AtomicFlowManager.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def ACond_for_9042030553971780173 (s₀ : State) : Literal := fromBool (s₀["var_i"]!! < s₀["expr_576_length"]!!)
def APost_for_9042030553971780173 (s₀ s₉ : State) : Prop := True
def ABody_for_9042030553971780173 (s₀ s₉ : State) : Prop := True
def AFor_for_9042030553971780173 (s₀ s₉ : State) : Prop := True

lemma for_9042030553971780173_cond_abs_of_code {s₀ fuel} : eval fuel for_9042030553971780173_cond (s₀) = (s₀, ACond_for_9042030553971780173 (s₀)) := by
  unfold eval ACond_for_9042030553971780173
  simp [for_9042030553971780173_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_9042030553971780173_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_9042030553971780173_post_concrete_of_code s₀ s₉ →
  Spec APost_for_9042030553971780173 s₀ s₉ := by
  unfold APost_for_9042030553971780173
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

lemma for_9042030553971780173_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_9042030553971780173_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_9042030553971780173 s₀ s₉ := by
  unfold ABody_for_9042030553971780173
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

lemma AZero_for_9042030553971780173 : ∀ s₀, isOk s₀ → ACond_for_9042030553971780173 (👌 s₀) = 0 → AFor_for_9042030553971780173 s₀ s₀ := by
  intro s₀ _ _
  trivial
lemma AOk_for_9042030553971780173 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_9042030553971780173 s₀ = 0 → ABody_for_9042030553971780173 s₀ s₂ → APost_for_9042030553971780173 s₂ s₄ → Spec AFor_for_9042030553971780173 s₄ s₅ → AFor_for_9042030553971780173 s₀ s₅
:= by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _ _
  trivial
lemma AContinue_for_9042030553971780173 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_9042030553971780173 s₀ = 0 → ABody_for_9042030553971780173 s₀ s₂ → Spec APost_for_9042030553971780173 (🧟s₂) s₄ → Spec AFor_for_9042030553971780173 s₄ s₅ → AFor_for_9042030553971780173 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _
  trivial
lemma ABreak_for_9042030553971780173 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_9042030553971780173 s₀ = 0 → ABody_for_9042030553971780173 s₀ s₂ → AFor_for_9042030553971780173 s₀ (🧟s₂) := by
  intro s₀ s₂ _ _ _ _
  trivial
lemma ALeave_for_9042030553971780173 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_9042030553971780173 s₀ = 0 → ABody_for_9042030553971780173 s₀ s₂ → AFor_for_9042030553971780173 s₀ s₂ := by
  intro s₀ s₂ _ _ _ _
  trivial

end

end AtomicFlowManager.Common
