import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_uint256_7838
import generated.AtomicFlowManager.AtomicFlowManager.cleanup_bool

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_3215443808221254969_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_3215443808221254969 (s₀ s₉ : State) : Prop := sorry

lemma if_3215443808221254969_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3215443808221254969_concrete_of_code s₀ s₉ →
  Spec A_if_3215443808221254969 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
