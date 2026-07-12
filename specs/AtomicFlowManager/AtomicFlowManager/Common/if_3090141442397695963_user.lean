import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.cleanup_bool

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_3090141442397695963_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_3090141442397695963 (s₀ s₉ : State) : Prop := if_3090141442397695963_concrete_of_code.1 s₀ s₉

lemma if_3090141442397695963_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3090141442397695963_concrete_of_code s₀ s₉ →
  Spec A_if_3090141442397695963 s₀ s₉ := by
  intro h
  simpa [A_if_3090141442397695963] using h

end

end AtomicFlowManager.Common
