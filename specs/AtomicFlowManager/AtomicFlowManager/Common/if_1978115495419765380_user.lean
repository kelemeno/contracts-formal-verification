import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1978115495419765380_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_1978115495419765380 (s₀ s₉ : State) : Prop := if_1978115495419765380_concrete_of_code.1 s₀ s₉

lemma if_1978115495419765380_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1978115495419765380_concrete_of_code s₀ s₉ →
  Spec A_if_1978115495419765380 s₀ s₉ := by
  intro h
  simpa [A_if_1978115495419765380] using h

end

end AtomicFlowManager.Common
