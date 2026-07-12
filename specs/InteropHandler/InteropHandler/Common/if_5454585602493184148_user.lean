import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_7346920477424193670
import generated.InteropHandler.InteropHandler.Common.block_4286530089781354155

import generated.InteropHandler.InteropHandler.Common.if_5454585602493184148_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

def A_if_5454585602493184148 (s₀ s₉ : State) : Prop := sorry

lemma if_5454585602493184148_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5454585602493184148_concrete_of_code s₀ s₉ →
  Spec A_if_5454585602493184148 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
