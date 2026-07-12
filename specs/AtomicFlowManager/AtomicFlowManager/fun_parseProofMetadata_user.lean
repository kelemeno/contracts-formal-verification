import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.allocate_and_zero_memory_struct_struct_ProofMetadata
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_uint256_dyn_calldata_7491
import generated.AtomicFlowManager.AtomicFlowManager.shift_left_uint256_uint8
import generated.AtomicFlowManager.AtomicFlowManager.Common.switch_1710979420930060748
import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool_7484
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256
import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool
import generated.AtomicFlowManager.AtomicFlowManager.cleanup_bool
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_348383089904533320
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5115675439432368612

import generated.AtomicFlowManager.AtomicFlowManager.fun_parseProofMetadata_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_fun_parseProofMetadata (var_result_mpos : Identifier) (var_proof_2893_offset var_proof_length : Literal) (s₀ s₉ : State) : Prop := fun_parseProofMetadata_concrete_of_code.1 var_result_mpos var_proof_2893_offset var_proof_length s₀ s₉

lemma fun_parseProofMetadata_abs_of_concrete {s₀ s₉ : State} {var_result_mpos var_proof_2893_offset var_proof_length} :
  Spec (fun_parseProofMetadata_concrete_of_code.1 var_result_mpos var_proof_2893_offset var_proof_length) s₀ s₉ →
  Spec (A_fun_parseProofMetadata var_result_mpos var_proof_2893_offset var_proof_length) s₀ s₉ := by
  intro h
  simpa [A_fun_parseProofMetadata] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
