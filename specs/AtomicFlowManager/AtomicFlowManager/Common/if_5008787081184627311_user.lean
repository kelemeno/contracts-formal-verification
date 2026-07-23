import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_bool_uint256_uint64_7917

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5008787081184627311_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_5008787081184627311 (s₀ s₉ : State) : Prop := if_5008787081184627311_concrete_of_code.1 s₀ s₉

lemma if_5008787081184627311_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5008787081184627311_concrete_of_code s₀ s₉ →
  Spec A_if_5008787081184627311 s₀ s₉ := by
  intro h
  simpa [A_if_5008787081184627311] using h

end

end AtomicFlowManager.Common
