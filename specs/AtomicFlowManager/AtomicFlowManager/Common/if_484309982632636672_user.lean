import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_484309982632636672_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_484309982632636672 (s₀ s₉ : State) : Prop := if_484309982632636672_concrete_of_code.1 s₀ s₉

lemma if_484309982632636672_abs_of_concrete {s₀ s₉ : State} :
  Spec if_484309982632636672_concrete_of_code s₀ s₉ →
  Spec A_if_484309982632636672 s₀ s₉ := by
  intro h
  simpa [A_if_484309982632636672] using h

end

end AtomicFlowManager.Common
