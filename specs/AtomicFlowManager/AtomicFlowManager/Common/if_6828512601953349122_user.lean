import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6828512601953349122_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_6828512601953349122 (s₀ s₉ : State) : Prop := if_6828512601953349122_concrete_of_code.1 s₀ s₉

lemma if_6828512601953349122_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6828512601953349122_concrete_of_code s₀ s₉ →
  Spec A_if_6828512601953349122 s₀ s₉ := by
  intro h
  simpa [A_if_6828512601953349122] using h

end

end AtomicFlowManager.Common
