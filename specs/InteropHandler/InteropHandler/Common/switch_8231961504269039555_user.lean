import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_993207518838446854
import generated.InteropHandler.InteropHandler.Common.if_5383038716103763640
import generated.InteropHandler.InteropHandler.Common.if_5441747811229036721
import generated.InteropHandler.InteropHandler.Common.block_1322021130774995196
import generated.InteropHandler.InteropHandler.Common.block_5819786208458579623
import generated.InteropHandler.InteropHandler.Common.if_5454585602493184148

import generated.InteropHandler.InteropHandler.Common.switch_8231961504269039555_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

def A_switch_8231961504269039555 (s₀ s₉ : State) : Prop :=
  switch_8231961504269039555_concrete_of_code.1 s₀ s₉
lemma switch_8231961504269039555_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8231961504269039555_concrete_of_code s₀ s₉ →
  Spec A_switch_8231961504269039555 s₀ s₉ := by
  intro h
  simpa [A_switch_8231961504269039555] using h

end

end InteropHandler.Common
