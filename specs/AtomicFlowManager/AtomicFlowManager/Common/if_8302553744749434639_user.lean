import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_uint256_7838

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_8302553744749434639_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_8302553744749434639 (s₀ s₉ : State) : Prop := if_8302553744749434639_concrete_of_code.1 s₀ s₉

lemma if_8302553744749434639_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8302553744749434639_concrete_of_code s₀ s₉ →
  Spec A_if_8302553744749434639 s₀ s₉ := by
  intro h
  simpa [A_if_8302553744749434639] using h

end

end AtomicFlowManager.Common
