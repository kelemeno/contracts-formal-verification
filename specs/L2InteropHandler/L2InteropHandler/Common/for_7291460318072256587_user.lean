import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_5653943394905820487
import generated.L2InteropHandler.L2InteropHandler.memory_array_index_access_enum_CallStatus_dyn
import generated.L2InteropHandler.L2InteropHandler.Common.block_5148743269212696695
import generated.L2InteropHandler.L2InteropHandler.Common.if_496874034733712113
import generated.L2InteropHandler.L2InteropHandler.Common.if_6279315680913726722
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation
import generated.L2InteropHandler.L2InteropHandler.Common.block_5180135173210496464
import generated.L2InteropHandler.L2InteropHandler.Common.block_8808803312049806377
import generated.L2InteropHandler.L2InteropHandler.Common.block_7763331755502755637
import generated.L2InteropHandler.L2InteropHandler.Common.block_4129078536961673341
import generated.L2InteropHandler.L2InteropHandler.Common.block_1150135081457496648
import generated.L2InteropHandler.L2InteropHandler.fun_formatEvmV1
import generated.L2InteropHandler.L2InteropHandler.Common.block_4873511899282199432
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes32_bytes_bytes
import generated.L2InteropHandler.L2InteropHandler.Common.block_7487716461786433003
import generated.L2InteropHandler.L2InteropHandler.Common.if_958493006745533688
import generated.L2InteropHandler.L2InteropHandler.Common.if_4919657989878521836
import generated.L2InteropHandler.L2InteropHandler.Common.if_7103836502326525636

import generated.L2InteropHandler.L2InteropHandler.Common.for_7291460318072256587_gen


namespace L2InteropHandler.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def ACond_for_7291460318072256587 (s₀ : State) : Literal := sorry 
def APost_for_7291460318072256587 (s₀ s₉ : State) : Prop := sorry
def ABody_for_7291460318072256587 (s₀ s₉ : State) : Prop := sorry
def AFor_for_7291460318072256587 (s₀ s₉ : State) : Prop := sorry

lemma for_7291460318072256587_cond_abs_of_code {s₀ fuel} : eval fuel for_7291460318072256587_cond (s₀) = (s₀, ACond_for_7291460318072256587 (s₀)) := by
  unfold eval ACond_for_7291460318072256587
  sorry

lemma for_7291460318072256587_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_7291460318072256587_post_concrete_of_code s₀ s₉ →
  Spec APost_for_7291460318072256587 s₀ s₉ := by
  sorry

lemma for_7291460318072256587_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_7291460318072256587_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_7291460318072256587 s₀ s₉ := by
  sorry

lemma AZero_for_7291460318072256587 : ∀ s₀, isOk s₀ → ACond_for_7291460318072256587 (👌 s₀) = 0 → AFor_for_7291460318072256587 s₀ s₀ := sorry
lemma AOk_for_7291460318072256587 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_7291460318072256587 s₀ = 0 → ABody_for_7291460318072256587 s₀ s₂ → APost_for_7291460318072256587 s₂ s₄ → Spec AFor_for_7291460318072256587 s₄ s₅ → AFor_for_7291460318072256587 s₀ s₅
:= sorry
lemma AContinue_for_7291460318072256587 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_7291460318072256587 s₀ = 0 → ABody_for_7291460318072256587 s₀ s₂ → Spec APost_for_7291460318072256587 (🧟s₂) s₄ → Spec AFor_for_7291460318072256587 s₄ s₅ → AFor_for_7291460318072256587 s₀ s₅ := sorry
lemma ABreak_for_7291460318072256587 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_7291460318072256587 s₀ = 0 → ABody_for_7291460318072256587 s₀ s₂ → AFor_for_7291460318072256587 s₀ (🧟s₂) := sorry
lemma ALeave_for_7291460318072256587 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_7291460318072256587 s₀ = 0 → ABody_for_7291460318072256587 s₀ s₂ → AFor_for_7291460318072256587 s₀ s₂ := sorry

end

end L2InteropHandler.Common
