import Clear.ReasoningPrinciple


import generated.L1Bridgehub.L1Bridgehub.Common.switch_8805183917919185541_gen


namespace L1Bridgehub.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_switch_8805183917919185541 (s₀ s₉ : State) : Prop := switch_8805183917919185541_concrete_of_code.1 s₀ s₉

lemma switch_8805183917919185541_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8805183917919185541_concrete_of_code s₀ s₉ →
  Spec A_switch_8805183917919185541 s₀ s₉ := by
  intro h
  simpa [A_switch_8805183917919185541] using h

end

end L1Bridgehub.Common
