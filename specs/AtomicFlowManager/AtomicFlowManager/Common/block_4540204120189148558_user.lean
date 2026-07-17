import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.checked_add_uint256

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4540204120189148558_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_4540204120189148558 (s₀ s₉ : State) : Prop := sorry

lemma block_4540204120189148558_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4540204120189148558_concrete_of_code s₀ s₉ →
  Spec A_block_4540204120189148558 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
