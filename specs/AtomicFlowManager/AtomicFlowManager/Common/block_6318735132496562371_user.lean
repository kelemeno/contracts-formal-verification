import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.constant_L2_MESSAGE_VERIFICATION_ADDR
import generated.AtomicFlowManager.AtomicFlowManager.cleanup_address

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6318735132496562371_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_6318735132496562371 (s₀ s₉ : State) : Prop := sorry

lemma block_6318735132496562371_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6318735132496562371_concrete_of_code s₀ s₉ →
  Spec A_block_6318735132496562371 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
