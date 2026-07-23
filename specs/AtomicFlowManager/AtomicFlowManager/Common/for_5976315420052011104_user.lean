import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_8780691482010514444
import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn

import generated.AtomicFlowManager.AtomicFlowManager.Common.for_5976315420052011104_gen


namespace AtomicFlowManager.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def ACond_for_5976315420052011104 (s₀ : State) : Literal := fromBool (s₀["var_i"]!! < s₀["length"]!!)
def APost_for_5976315420052011104 (s₀ s₉ : State) : Prop := for_5976315420052011104_post_concrete_of_code.1 s₀ s₉
def ABody_for_5976315420052011104 (s₀ s₉ : State) : Prop := for_5976315420052011104_body_concrete_of_code.1 s₀ s₉
def AFor_for_5976315420052011104 (s₀ s₉ : State) : Prop := True

lemma for_5976315420052011104_cond_abs_of_code {s₀ fuel} : eval fuel for_5976315420052011104_cond (s₀) = (s₀, ACond_for_5976315420052011104 (s₀)) := by
  unfold eval ACond_for_5976315420052011104
  simp [for_5976315420052011104_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_5976315420052011104_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_5976315420052011104_post_concrete_of_code s₀ s₉ →
  Spec APost_for_5976315420052011104 s₀ s₉ := by
  intro h
  simpa [APost_for_5976315420052011104] using h

lemma for_5976315420052011104_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_5976315420052011104_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_5976315420052011104 s₀ s₉ := by
  intro h
  simpa [ABody_for_5976315420052011104] using h

lemma AZero_for_5976315420052011104 : ∀ s₀, isOk s₀ → ACond_for_5976315420052011104 (👌 s₀) = 0 → AFor_for_5976315420052011104 s₀ s₀ := by intros; trivial
lemma AOk_for_5976315420052011104 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_5976315420052011104 s₀ = 0 → ABody_for_5976315420052011104 s₀ s₂ → APost_for_5976315420052011104 s₂ s₄ → Spec AFor_for_5976315420052011104 s₄ s₅ → AFor_for_5976315420052011104 s₀ s₅
:= by intros; trivial
lemma AContinue_for_5976315420052011104 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_5976315420052011104 s₀ = 0 → ABody_for_5976315420052011104 s₀ s₂ → Spec APost_for_5976315420052011104 (🧟s₂) s₄ → Spec AFor_for_5976315420052011104 s₄ s₅ → AFor_for_5976315420052011104 s₀ s₅ := by intros; trivial
lemma ABreak_for_5976315420052011104 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_5976315420052011104 s₀ = 0 → ABody_for_5976315420052011104 s₀ s₂ → AFor_for_5976315420052011104 s₀ (🧟s₂) := by intros; trivial
lemma ALeave_for_5976315420052011104 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_5976315420052011104 s₀ = 0 → ABody_for_5976315420052011104 s₀ s₂ → AFor_for_5976315420052011104 s₀ s₂ := by intros; trivial

end

end AtomicFlowManager.Common
