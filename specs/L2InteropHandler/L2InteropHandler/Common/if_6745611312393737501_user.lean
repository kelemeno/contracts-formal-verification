import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_6342950090026176044
import generated.L2InteropHandler.L2InteropHandler.Common.block_1885029154092524249

import generated.L2InteropHandler.L2InteropHandler.Common.if_6745611312393737501_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_if_6745611312393737501 (s₀ s₉ : State) : Prop := sorry

lemma if_6745611312393737501_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6745611312393737501_concrete_of_code s₀ s₉ →
  Spec A_if_6745611312393737501 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common
