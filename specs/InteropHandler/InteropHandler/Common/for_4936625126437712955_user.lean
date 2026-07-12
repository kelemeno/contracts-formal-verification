import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_8272958829832772907
import generated.InteropHandler.InteropHandler.Common.if_2148087268121722474
import generated.InteropHandler.InteropHandler.Common.if_97214993889306344
import generated.InteropHandler.InteropHandler.Common.block_6876290329527675630
import generated.InteropHandler.InteropHandler.abi_decode_bytes1_fromMemory
import generated.InteropHandler.InteropHandler.Common.block_5871605398089026784
import generated.InteropHandler.InteropHandler.abi_decode_bool_fromMemory
import generated.InteropHandler.InteropHandler.Common.block_3205230576799817907
import generated.InteropHandler.InteropHandler.abi_decode_address_fromMemory
import generated.InteropHandler.InteropHandler.Common.block_1343836995267101158
import generated.InteropHandler.InteropHandler.Common.block_7778734710101628289
import generated.InteropHandler.InteropHandler.Common.if_2715977721633744624
import generated.InteropHandler.InteropHandler.Common.block_5373162064653865112
import generated.InteropHandler.InteropHandler.abi_decode_bytes_fromMemory
import generated.InteropHandler.InteropHandler.Common.block_1597461583734612352

import generated.InteropHandler.InteropHandler.Common.for_4936625126437712955_gen


namespace InteropHandler.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def ACond_for_4936625126437712955 (s₀ : State) : Literal := sorry 
def APost_for_4936625126437712955 (s₀ s₉ : State) : Prop := sorry
def ABody_for_4936625126437712955 (s₀ s₉ : State) : Prop := sorry
def AFor_for_4936625126437712955 (s₀ s₉ : State) : Prop := sorry

lemma for_4936625126437712955_cond_abs_of_code {s₀ fuel} : eval fuel for_4936625126437712955_cond (s₀) = (s₀, ACond_for_4936625126437712955 (s₀)) := by
  unfold eval ACond_for_4936625126437712955
  sorry

lemma for_4936625126437712955_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_4936625126437712955_post_concrete_of_code s₀ s₉ →
  Spec APost_for_4936625126437712955 s₀ s₉ := by
  sorry

lemma for_4936625126437712955_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_4936625126437712955_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_4936625126437712955 s₀ s₉ := by
  sorry

lemma AZero_for_4936625126437712955 : ∀ s₀, isOk s₀ → ACond_for_4936625126437712955 (👌 s₀) = 0 → AFor_for_4936625126437712955 s₀ s₀ := sorry
lemma AOk_for_4936625126437712955 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_4936625126437712955 s₀ = 0 → ABody_for_4936625126437712955 s₀ s₂ → APost_for_4936625126437712955 s₂ s₄ → Spec AFor_for_4936625126437712955 s₄ s₅ → AFor_for_4936625126437712955 s₀ s₅
:= sorry
lemma AContinue_for_4936625126437712955 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_4936625126437712955 s₀ = 0 → ABody_for_4936625126437712955 s₀ s₂ → Spec APost_for_4936625126437712955 (🧟s₂) s₄ → Spec AFor_for_4936625126437712955 s₄ s₅ → AFor_for_4936625126437712955 s₀ s₅ := sorry
lemma ABreak_for_4936625126437712955 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_4936625126437712955 s₀ = 0 → ABody_for_4936625126437712955 s₀ s₂ → AFor_for_4936625126437712955 s₀ (🧟s₂) := sorry
lemma ALeave_for_4936625126437712955 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_4936625126437712955 s₀ = 0 → ABody_for_4936625126437712955 s₀ s₂ → AFor_for_4936625126437712955 s₀ s₂ := sorry

end

end InteropHandler.Common
