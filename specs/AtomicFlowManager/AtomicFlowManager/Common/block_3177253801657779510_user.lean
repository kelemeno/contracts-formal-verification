import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_available_length_bytes
import generated.AtomicFlowManager.AtomicFlowManager.fun_encodeInteropBundleHash
import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7397
import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3177253801657779510_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_3177253801657779510 (s₀ s₉ : State) : Prop := block_3177253801657779510_concrete_of_code.1 s₀ s₉

lemma block_3177253801657779510_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3177253801657779510_concrete_of_code s₀ s₉ →
  Spec A_block_3177253801657779510 s₀ s₉ := by
  intro h
  simpa [A_block_3177253801657779510] using h

end

end AtomicFlowManager.Common
