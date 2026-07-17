import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_array_bytes32_dyn_calldata_array_uint256_dyn_calldata_uint64_uint256

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1859557971115827348_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_1859557971115827348 (s₀ s₉ : State) : Prop := sorry

lemma block_1859557971115827348_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1859557971115827348_concrete_of_code s₀ s₉ →
  Spec A_block_1859557971115827348 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
