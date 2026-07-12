import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8461366879169494547
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_array_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_173430096193575997
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5924889543902721644

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_array_bytes32_dyn_calldata_array_uint256_dyn_calldata_uint64_uint256_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_abi_encode_array_bytes32_dyn_calldata_array_uint256_dyn_calldata_uint64_uint256 (tail : Identifier) (headStart value0 value1 value2 value3 value4 value5 : Literal) (s₀ s₉ : State) : Prop := abi_encode_array_bytes32_dyn_calldata_array_uint256_dyn_calldata_uint64_uint256_concrete_of_code.1 tail headStart value0 value1 value2 value3 value4 value5 s₀ s₉

lemma abi_encode_array_bytes32_dyn_calldata_array_uint256_dyn_calldata_uint64_uint256_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2 value3 value4 value5} :
  Spec (abi_encode_array_bytes32_dyn_calldata_array_uint256_dyn_calldata_uint64_uint256_concrete_of_code.1 tail headStart value0 value1 value2 value3 value4 value5) s₀ s₉ →
  Spec (A_abi_encode_array_bytes32_dyn_calldata_array_uint256_dyn_calldata_uint64_uint256 tail headStart value0 value1 value2 value3 value4 value5) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_array_bytes32_dyn_calldata_array_uint256_dyn_calldata_uint64_uint256] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
