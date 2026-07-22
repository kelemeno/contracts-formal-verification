import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_8272958829832772907
import generated.L2InteropHandler.L2InteropHandler.Common.if_2862847678296118633
import generated.L2InteropHandler.L2InteropHandler.Common.if_2620756797971343280
import generated.L2InteropHandler.L2InteropHandler.Common.block_4764315573689646434
import generated.L2InteropHandler.L2InteropHandler.abi_decode_bytes1_fromMemory
import generated.L2InteropHandler.L2InteropHandler.Common.block_9043014988112682862
import generated.L2InteropHandler.L2InteropHandler.abi_decode_bool_fromMemory
import generated.L2InteropHandler.L2InteropHandler.Common.block_6044862068185174769
import generated.L2InteropHandler.L2InteropHandler.abi_decode_address_fromMemory
import generated.L2InteropHandler.L2InteropHandler.Common.block_9000817459521719406
import generated.L2InteropHandler.L2InteropHandler.Common.block_6528822718374154334
import generated.L2InteropHandler.L2InteropHandler.Common.if_2715977721633744624
import generated.L2InteropHandler.L2InteropHandler.Common.block_7304647318122259887
import generated.L2InteropHandler.L2InteropHandler.abi_decode_bytes_fromMemory
import generated.L2InteropHandler.L2InteropHandler.Common.block_1597461583734612352

import generated.L2InteropHandler.L2InteropHandler.Common.for_6430914214554261284_gen


namespace L2InteropHandler.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def ACond_for_6430914214554261284 (s₀ : State) : Literal := sorry 
def APost_for_6430914214554261284 (s₀ s₉ : State) : Prop := sorry
def ABody_for_6430914214554261284 (s₀ s₉ : State) : Prop := sorry
def AFor_for_6430914214554261284 (s₀ s₉ : State) : Prop := sorry

lemma for_6430914214554261284_cond_abs_of_code {s₀ fuel} : eval fuel for_6430914214554261284_cond (s₀) = (s₀, ACond_for_6430914214554261284 (s₀)) := by
  unfold eval ACond_for_6430914214554261284
  sorry

lemma for_6430914214554261284_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_6430914214554261284_post_concrete_of_code s₀ s₉ →
  Spec APost_for_6430914214554261284 s₀ s₉ := by
  sorry

lemma for_6430914214554261284_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_6430914214554261284_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_6430914214554261284 s₀ s₉ := by
  sorry

lemma AZero_for_6430914214554261284 : ∀ s₀, isOk s₀ → ACond_for_6430914214554261284 (👌 s₀) = 0 → AFor_for_6430914214554261284 s₀ s₀ := sorry
lemma AOk_for_6430914214554261284 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_6430914214554261284 s₀ = 0 → ABody_for_6430914214554261284 s₀ s₂ → APost_for_6430914214554261284 s₂ s₄ → Spec AFor_for_6430914214554261284 s₄ s₅ → AFor_for_6430914214554261284 s₀ s₅
:= sorry
lemma AContinue_for_6430914214554261284 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_6430914214554261284 s₀ = 0 → ABody_for_6430914214554261284 s₀ s₂ → Spec APost_for_6430914214554261284 (🧟s₂) s₄ → Spec AFor_for_6430914214554261284 s₄ s₅ → AFor_for_6430914214554261284 s₀ s₅ := sorry
lemma ABreak_for_6430914214554261284 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_6430914214554261284 s₀ = 0 → ABody_for_6430914214554261284 s₀ s₂ → AFor_for_6430914214554261284 s₀ (🧟s₂) := sorry
lemma ALeave_for_6430914214554261284 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_6430914214554261284 s₀ = 0 → ABody_for_6430914214554261284 s₀ s₂ → AFor_for_6430914214554261284 s₀ s₂ := sorry

end

end L2InteropHandler.Common
