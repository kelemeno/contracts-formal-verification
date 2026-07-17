import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x11

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_4432928539203713149_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_4432928539203713149 (s₀ s₉ : State) : Prop := sorry

lemma if_4432928539203713149_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4432928539203713149_concrete_of_code s₀ s₉ →
  Spec A_if_4432928539203713149 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
