import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.increment_uint256

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5390487839625046806_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_5390487839625046806 (s₀ s₉ : State) : Prop := if_5390487839625046806_concrete_of_code.1 s₀ s₉

lemma if_5390487839625046806_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5390487839625046806_concrete_of_code s₀ s₉ →
  Spec A_if_5390487839625046806 s₀ s₉ := by
  intro h
  simpa [A_if_5390487839625046806] using h

end

end AtomicFlowManager.Common
