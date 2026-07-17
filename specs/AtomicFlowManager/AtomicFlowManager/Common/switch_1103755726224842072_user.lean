import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.switch_1103755726224842072_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_switch_1103755726224842072 (s₀ s₉ : State) : Prop := sorry

lemma switch_1103755726224842072_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_1103755726224842072_concrete_of_code s₀ s₉ →
  Spec A_switch_1103755726224842072 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
