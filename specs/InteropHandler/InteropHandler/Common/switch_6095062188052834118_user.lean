import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.switch_6095062188052834118_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_switch_6095062188052834118 (s₀ s₉ : State) : Prop := sorry

lemma switch_6095062188052834118_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_6095062188052834118_concrete_of_code s₀ s₉ →
  Spec A_switch_6095062188052834118 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
