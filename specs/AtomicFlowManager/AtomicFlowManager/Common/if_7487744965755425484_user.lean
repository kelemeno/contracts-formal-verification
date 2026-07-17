import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_7487744965755425484_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_7487744965755425484 (s₀ s₉ : State) : Prop := sorry

lemma if_7487744965755425484_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7487744965755425484_concrete_of_code s₀ s₉ →
  Spec A_if_7487744965755425484 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
