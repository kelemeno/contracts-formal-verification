import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.revert_forward

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_7069222774777857031_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_7069222774777857031 (s₀ s₉ : State) : Prop := if_7069222774777857031_concrete_of_code.1 s₀ s₉

lemma if_7069222774777857031_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7069222774777857031_concrete_of_code s₀ s₉ →
  Spec A_if_7069222774777857031 s₀ s₉ := by
  intro h
  simpa [A_if_7069222774777857031] using h

end

end AtomicFlowManager.Common
