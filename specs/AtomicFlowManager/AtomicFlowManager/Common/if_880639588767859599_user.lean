import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_bytes32_bytes32_enum_LegState

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_880639588767859599_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_880639588767859599 (s₀ s₉ : State) : Prop := sorry

lemma if_880639588767859599_abs_of_concrete {s₀ s₉ : State} :
  Spec if_880639588767859599_concrete_of_code s₀ s₉ →
  Spec A_if_880639588767859599 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
