import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x11

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5196681927906208124_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_5196681927906208124 (s₀ s₉ : State) : Prop := if_5196681927906208124_concrete_of_code.1 s₀ s₉

lemma if_5196681927906208124_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5196681927906208124_concrete_of_code s₀ s₉ →
  Spec A_if_5196681927906208124 s₀ s₉ := by
  intro h
  simpa [A_if_5196681927906208124] using h

end

end AtomicFlowManager.Common
