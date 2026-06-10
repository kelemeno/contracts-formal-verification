import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_2328457584417225796
import generated.L1Bridgehub.L1Bridgehub.Common.if_2352170140006762975

import generated.L1Bridgehub.L1Bridgehub.Common.switch_8539157929318587848_gen


namespace L1Bridgehub.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common 

def A_switch_8539157929318587848 (s₀ s₉ : State) : Prop := switch_8539157929318587848_concrete_of_code.1 s₀ s₉

lemma switch_8539157929318587848_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8539157929318587848_concrete_of_code s₀ s₉ →
  Spec A_switch_8539157929318587848 s₀ s₉ := by
  intro h
  simpa [A_switch_8539157929318587848] using h

end

end L1Bridgehub.Common
