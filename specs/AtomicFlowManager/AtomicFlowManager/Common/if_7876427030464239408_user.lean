import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_uint256_7838

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_7876427030464239408_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_7876427030464239408 (s₀ s₉ : State) : Prop := if_7876427030464239408_concrete_of_code.1 s₀ s₉

lemma if_7876427030464239408_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7876427030464239408_concrete_of_code s₀ s₉ →
  Spec A_if_7876427030464239408 s₀ s₉ := by
  intro h
  simpa [A_if_7876427030464239408] using h

end

end AtomicFlowManager.Common
