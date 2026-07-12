import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_8272958829832772907_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_8272958829832772907 (s₀ s₉ : State) : Prop := if_8272958829832772907_concrete_of_code.1 s₀ s₉

lemma if_8272958829832772907_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8272958829832772907_concrete_of_code s₀ s₉ →
  Spec A_if_8272958829832772907 s₀ s₉ := by
  intro h
  simpa [A_if_8272958829832772907] using h

end

end AtomicFlowManager.Common
