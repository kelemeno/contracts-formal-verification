import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.switch_5192518044804447739_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_switch_5192518044804447739 (s₀ s₉ : State) : Prop := sorry

lemma switch_5192518044804447739_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_5192518044804447739_concrete_of_code s₀ s₉ →
  Spec A_switch_5192518044804447739 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
