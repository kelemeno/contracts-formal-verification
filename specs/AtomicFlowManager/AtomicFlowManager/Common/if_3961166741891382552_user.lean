import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x11

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_3961166741891382552_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_3961166741891382552 (s₀ s₉ : State) : Prop := if_3961166741891382552_concrete_of_code.1 s₀ s₉

lemma if_3961166741891382552_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3961166741891382552_concrete_of_code s₀ s₉ →
  Spec A_if_3961166741891382552 s₀ s₉ := by
  intro h
  simpa [A_if_3961166741891382552] using h

end

end AtomicFlowManager.Common
