import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4495411844040129084_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_4495411844040129084 (s₀ s₉ : State) : Prop := sorry

lemma block_4495411844040129084_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4495411844040129084_concrete_of_code s₀ s₉ →
  Spec A_block_4495411844040129084 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
