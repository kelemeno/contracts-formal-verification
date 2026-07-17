import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_uint256_7838
import generated.AtomicFlowManager.AtomicFlowManager.cleanup_bool

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5583277985193582718_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_5583277985193582718 (s₀ s₉ : State) : Prop := sorry

lemma if_5583277985193582718_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5583277985193582718_concrete_of_code s₀ s₉ →
  Spec A_if_5583277985193582718 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
