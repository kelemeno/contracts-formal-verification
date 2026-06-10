import Clear.ReasoningPrinciple


import generated.L1Bridgehub.L1Bridgehub.Common.switch_2379653503816674189_gen


namespace L1Bridgehub.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_switch_2379653503816674189 (s₀ s₉ : State) : Prop := switch_2379653503816674189_concrete_of_code.1 s₀ s₉

lemma switch_2379653503816674189_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_2379653503816674189_concrete_of_code s₀ s₉ →
  Spec A_switch_2379653503816674189 s₀ s₉ := by
  intro h
  simpa [A_switch_2379653503816674189] using h

end

end L1Bridgehub.Common
