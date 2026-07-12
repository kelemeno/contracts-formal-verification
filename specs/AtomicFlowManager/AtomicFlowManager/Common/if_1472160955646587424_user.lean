import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1472160955646587424_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_1472160955646587424 (s₀ s₉ : State) : Prop := if_1472160955646587424_concrete_of_code.1 s₀ s₉

lemma if_1472160955646587424_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1472160955646587424_concrete_of_code s₀ s₉ →
  Spec A_if_1472160955646587424 s₀ s₉ := by
  intro h
  simpa [A_if_1472160955646587424] using h

end

end AtomicFlowManager.Common
