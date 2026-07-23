import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.switch_6095062188052834118_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_switch_6095062188052834118 (s₀ s₉ : State) : Prop := switch_6095062188052834118_concrete_of_code.1 s₀ s₉

lemma switch_6095062188052834118_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_6095062188052834118_concrete_of_code s₀ s₉ →
  Spec A_switch_6095062188052834118 s₀ s₉ := by
  intro h
  simpa [A_switch_6095062188052834118] using h

end

end L2InteropHandler.Common
