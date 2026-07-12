import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_1313947117152468440
import generated.InteropHandler.InteropHandler.memory_array_index_access_enum_CallStatus_dyn
import generated.InteropHandler.InteropHandler.Common.block_2435830699431932975
import generated.InteropHandler.InteropHandler.Common.if_5072805428743413223
import generated.InteropHandler.InteropHandler.Common.if_5123539838950373489
import generated.InteropHandler.InteropHandler.finalize_allocation
import generated.InteropHandler.InteropHandler.Common.block_2534382867797823206
import generated.InteropHandler.InteropHandler.Common.block_3811156559814846904
import generated.InteropHandler.InteropHandler.Common.block_8202435018202551211
import generated.InteropHandler.InteropHandler.Common.block_3188991857275442231
import generated.InteropHandler.InteropHandler.Common.block_5805611883088407543
import generated.InteropHandler.InteropHandler.fun_formatEvmV1
import generated.InteropHandler.InteropHandler.Common.block_3148999116192219682
import generated.InteropHandler.InteropHandler.abi_encode_bytes32_bytes_bytes
import generated.InteropHandler.InteropHandler.Common.block_5660342622014480655
import generated.InteropHandler.InteropHandler.Common.if_1981605665850973762
import generated.InteropHandler.InteropHandler.Common.if_3549384021840798378
import generated.InteropHandler.InteropHandler.Common.if_4647531265572920007

import generated.InteropHandler.InteropHandler.Common.for_8649674080430825952_gen


namespace InteropHandler.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def ACond_for_8649674080430825952 (s₀ : State) : Literal := sorry 
def APost_for_8649674080430825952 (s₀ s₉ : State) : Prop := sorry
def ABody_for_8649674080430825952 (s₀ s₉ : State) : Prop := sorry
def AFor_for_8649674080430825952 (s₀ s₉ : State) : Prop := sorry

lemma for_8649674080430825952_cond_abs_of_code {s₀ fuel} : eval fuel for_8649674080430825952_cond (s₀) = (s₀, ACond_for_8649674080430825952 (s₀)) := by
  unfold eval ACond_for_8649674080430825952
  sorry

lemma for_8649674080430825952_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_8649674080430825952_post_concrete_of_code s₀ s₉ →
  Spec APost_for_8649674080430825952 s₀ s₉ := by
  sorry

lemma for_8649674080430825952_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_8649674080430825952_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_8649674080430825952 s₀ s₉ := by
  sorry

lemma AZero_for_8649674080430825952 : ∀ s₀, isOk s₀ → ACond_for_8649674080430825952 (👌 s₀) = 0 → AFor_for_8649674080430825952 s₀ s₀ := sorry
lemma AOk_for_8649674080430825952 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_8649674080430825952 s₀ = 0 → ABody_for_8649674080430825952 s₀ s₂ → APost_for_8649674080430825952 s₂ s₄ → Spec AFor_for_8649674080430825952 s₄ s₅ → AFor_for_8649674080430825952 s₀ s₅
:= sorry
lemma AContinue_for_8649674080430825952 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_8649674080430825952 s₀ = 0 → ABody_for_8649674080430825952 s₀ s₂ → Spec APost_for_8649674080430825952 (🧟s₂) s₄ → Spec AFor_for_8649674080430825952 s₄ s₅ → AFor_for_8649674080430825952 s₀ s₅ := sorry
lemma ABreak_for_8649674080430825952 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_8649674080430825952 s₀ = 0 → ABody_for_8649674080430825952 s₀ s₂ → AFor_for_8649674080430825952 s₀ (🧟s₂) := sorry
lemma ALeave_for_8649674080430825952 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_8649674080430825952 s₀ = 0 → ABody_for_8649674080430825952 s₀ s₂ → AFor_for_8649674080430825952 s₀ s₂ := sorry

end

end InteropHandler.Common
