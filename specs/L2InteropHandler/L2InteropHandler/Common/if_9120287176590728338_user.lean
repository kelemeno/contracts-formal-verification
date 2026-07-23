import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_8270347550785865638
import generated.L2InteropHandler.L2InteropHandler.Common.block_1885029154092524249

import generated.L2InteropHandler.L2InteropHandler.Common.if_9120287176590728338_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_if_9120287176590728338 (s₀ s₉ : State) : Prop := if_9120287176590728338_concrete_of_code.1 s₀ s₉

lemma if_9120287176590728338_abs_of_concrete {s₀ s₉ : State} :
  Spec if_9120287176590728338_concrete_of_code s₀ s₉ →
  Spec A_if_9120287176590728338 s₀ s₉ := by
  intro h
  simpa [A_if_9120287176590728338] using h

end

end L2InteropHandler.Common
