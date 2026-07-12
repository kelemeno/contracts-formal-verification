import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5542951638588498653
import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5973990049402045337
import generated.AtomicFlowManager.AtomicFlowManager.cleanup_address
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6945630744096063339
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8468136830088968592
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_bytes
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_9097063384830582942
import generated.AtomicFlowManager.AtomicFlowManager.revert_forward
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6066731633345594937
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bool_fromMemory
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5390487839625046806
import generated.AtomicFlowManager.AtomicFlowManager.increment_uint256

import generated.AtomicFlowManager.AtomicFlowManager.Common.for_7993347358814374560_gen


namespace AtomicFlowManager.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def ACond_for_7993347358814374560 (s₀ : State) : Literal := fromBool (s₀["var_i"]!! < s₀["length"]!!)
def APost_for_7993347358814374560 (s₀ s₉ : State) : Prop := True
def ABody_for_7993347358814374560 (s₀ s₉ : State) : Prop := True
def AFor_for_7993347358814374560 (s₀ s₉ : State) : Prop := True

lemma for_7993347358814374560_cond_abs_of_code {s₀ fuel} : eval fuel for_7993347358814374560_cond (s₀) = (s₀, ACond_for_7993347358814374560 (s₀)) := by
  unfold eval ACond_for_7993347358814374560
  simp [for_7993347358814374560_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_7993347358814374560_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_7993347358814374560_post_concrete_of_code s₀ s₉ →
  Spec APost_for_7993347358814374560 s₀ s₉ := by
  unfold APost_for_7993347358814374560
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

lemma for_7993347358814374560_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_7993347358814374560_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_7993347358814374560 s₀ s₉ := by
  unfold ABody_for_7993347358814374560
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

lemma AZero_for_7993347358814374560 : ∀ s₀, isOk s₀ → ACond_for_7993347358814374560 (👌 s₀) = 0 → AFor_for_7993347358814374560 s₀ s₀ := by
  intro s₀ _ _
  trivial
lemma AOk_for_7993347358814374560 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_7993347358814374560 s₀ = 0 → ABody_for_7993347358814374560 s₀ s₂ → APost_for_7993347358814374560 s₂ s₄ → Spec AFor_for_7993347358814374560 s₄ s₅ → AFor_for_7993347358814374560 s₀ s₅
:= by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _ _
  trivial
lemma AContinue_for_7993347358814374560 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_7993347358814374560 s₀ = 0 → ABody_for_7993347358814374560 s₀ s₂ → Spec APost_for_7993347358814374560 (🧟s₂) s₄ → Spec AFor_for_7993347358814374560 s₄ s₅ → AFor_for_7993347358814374560 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _
  trivial
lemma ABreak_for_7993347358814374560 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_7993347358814374560 s₀ = 0 → ABody_for_7993347358814374560 s₀ s₂ → AFor_for_7993347358814374560 s₀ (🧟s₂) := by
  intro s₀ s₂ _ _ _ _
  trivial
lemma ALeave_for_7993347358814374560 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_7993347358814374560 s₀ = 0 → ABody_for_7993347358814374560 s₀ s₂ → AFor_for_7993347358814374560 s₀ s₂ := by
  intro s₀ s₂ _ _ _ _
  trivial

end

end AtomicFlowManager.Common
