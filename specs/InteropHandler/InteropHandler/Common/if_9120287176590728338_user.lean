import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_8270347550785865638
import generated.InteropHandler.InteropHandler.Common.block_1885029154092524249

import generated.InteropHandler.InteropHandler.Common.if_9120287176590728338_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

def A_if_9120287176590728338 (s₀ s₉ : State) : Prop := sorry

lemma if_9120287176590728338_abs_of_concrete {s₀ s₉ : State} :
  Spec if_9120287176590728338_concrete_of_code s₀ s₉ →
  Spec A_if_9120287176590728338 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
