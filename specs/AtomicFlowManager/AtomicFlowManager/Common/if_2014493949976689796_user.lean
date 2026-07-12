import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2014493949976689796_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_2014493949976689796 (s₀ s₉ : State) : Prop := if_2014493949976689796_concrete_of_code.1 s₀ s₉

lemma if_2014493949976689796_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2014493949976689796_concrete_of_code s₀ s₉ →
  Spec A_if_2014493949976689796 s₀ s₉ := by
  intro h
  simpa [A_if_2014493949976689796] using h

end

end AtomicFlowManager.Common
