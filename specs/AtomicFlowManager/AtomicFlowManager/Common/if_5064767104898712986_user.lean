import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5064767104898712986_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_5064767104898712986 (s₀ s₉ : State) : Prop := if_5064767104898712986_concrete_of_code.1 s₀ s₉

lemma if_5064767104898712986_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5064767104898712986_concrete_of_code s₀ s₉ →
  Spec A_if_5064767104898712986 s₀ s₉ := by
  intro h
  simpa [A_if_5064767104898712986] using h

end

end AtomicFlowManager.Common
