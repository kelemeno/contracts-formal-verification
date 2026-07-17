import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.increment_uint256

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8443406799220370040_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_8443406799220370040 (s₀ s₉ : State) : Prop := sorry

lemma block_8443406799220370040_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8443406799220370040_concrete_of_code s₀ s₉ →
  Spec A_block_8443406799220370040 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
