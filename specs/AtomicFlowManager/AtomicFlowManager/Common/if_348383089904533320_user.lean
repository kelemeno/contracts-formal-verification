import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_348383089904533320_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_348383089904533320 (s₀ s₉ : State) : Prop := if_348383089904533320_concrete_of_code.1 s₀ s₉

lemma if_348383089904533320_abs_of_concrete {s₀ s₉ : State} :
  Spec if_348383089904533320_concrete_of_code s₀ s₉ →
  Spec A_if_348383089904533320 s₀ s₉ := by
  intro h
  simpa [A_if_348383089904533320] using h

end

end AtomicFlowManager.Common
