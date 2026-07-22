import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_7703584565394306917
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation
import generated.L2InteropHandler.L2InteropHandler.Common.if_7750633916235742269

import generated.L2InteropHandler.L2InteropHandler.Common.if_1105747289899550652_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_if_1105747289899550652 (s₀ s₉ : State) : Prop := sorry

lemma if_1105747289899550652_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1105747289899550652_concrete_of_code s₀ s₉ →
  Spec A_if_1105747289899550652 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common
