import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.fun_chainIdLeafHash
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7662516168618258410_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_7662516168618258410 (s₀ s₉ : State) : Prop := sorry

lemma block_7662516168618258410_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7662516168618258410_concrete_of_code s₀ s₉ →
  Spec A_block_7662516168618258410 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
