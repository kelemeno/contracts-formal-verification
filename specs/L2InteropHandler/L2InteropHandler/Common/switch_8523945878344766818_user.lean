import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.switch_8523945878344766818_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_switch_8523945878344766818 (s₀ s₉ : State) : Prop := sorry

lemma switch_8523945878344766818_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8523945878344766818_concrete_of_code s₀ s₉ →
  Spec A_switch_8523945878344766818 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common
