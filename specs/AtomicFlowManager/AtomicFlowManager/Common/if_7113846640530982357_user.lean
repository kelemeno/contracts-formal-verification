import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x11

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_7113846640530982357_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_7113846640530982357 (s₀ s₉ : State) : Prop := if_7113846640530982357_concrete_of_code.1 s₀ s₉

lemma if_7113846640530982357_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7113846640530982357_concrete_of_code s₀ s₉ →
  Spec A_if_7113846640530982357 s₀ s₉ := by
  intro h
  simpa [A_if_7113846640530982357] using h

end

end AtomicFlowManager.Common
