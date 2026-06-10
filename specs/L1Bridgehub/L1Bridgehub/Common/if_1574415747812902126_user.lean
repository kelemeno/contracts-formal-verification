import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_9186858324704191393
import generated.L1Bridgehub.L1Bridgehub.finalize_allocation
import generated.L1Bridgehub.L1Bridgehub.Common.if_8641178249089768828

import generated.L1Bridgehub.L1Bridgehub.Common.if_1574415747812902126_gen


namespace L1Bridgehub.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common generated.L1Bridgehub L1Bridgehub

def A_if_1574415747812902126 (s₀ s₉ : State) : Prop := if_1574415747812902126_concrete_of_code.1 s₀ s₉

lemma if_1574415747812902126_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1574415747812902126_concrete_of_code s₀ s₉ →
  Spec A_if_1574415747812902126 s₀ s₉ := by
  intro h
  simpa [A_if_1574415747812902126] using h

end

end L1Bridgehub.Common
