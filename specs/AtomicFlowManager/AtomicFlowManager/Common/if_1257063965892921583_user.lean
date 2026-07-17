import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1257063965892921583_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_1257063965892921583 (s₀ s₉ : State) : Prop := sorry

lemma if_1257063965892921583_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1257063965892921583_concrete_of_code s₀ s₉ →
  Spec A_if_1257063965892921583 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
