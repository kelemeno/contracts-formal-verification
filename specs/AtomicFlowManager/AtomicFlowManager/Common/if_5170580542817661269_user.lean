import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5170580542817661269_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_5170580542817661269 (s₀ s₉ : State) : Prop := sorry

lemma if_5170580542817661269_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5170580542817661269_concrete_of_code s₀ s₉ →
  Spec A_if_5170580542817661269 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
