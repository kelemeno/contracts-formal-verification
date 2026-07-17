import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6513072199354926456_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_6513072199354926456 (s₀ s₉ : State) : Prop := sorry

lemma if_6513072199354926456_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6513072199354926456_concrete_of_code s₀ s₉ →
  Spec A_if_6513072199354926456 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
