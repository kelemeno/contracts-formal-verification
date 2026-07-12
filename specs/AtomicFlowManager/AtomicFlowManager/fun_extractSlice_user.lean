import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_9087881277877411820
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x11
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4370574319895427309
import generated.AtomicFlowManager.AtomicFlowManager.array_allocation_size_array_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1121944688373970425
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8562236278678738811
import generated.AtomicFlowManager.AtomicFlowManager.Common.for_423567071893050842
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_uint256_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn

import generated.AtomicFlowManager.AtomicFlowManager.fun_extractSlice_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_fun_extractSlice (var_slice_mpos : Identifier) (var_proof_3296_offset var__proof_length var_left var_right : Literal) (s₀ s₉ : State) : Prop := fun_extractSlice_concrete_of_code.1 var_slice_mpos var_proof_3296_offset var__proof_length var_left var_right s₀ s₉

lemma fun_extractSlice_abs_of_concrete {s₀ s₉ : State} {var_slice_mpos var_proof_3296_offset var__proof_length var_left var_right} :
  Spec (fun_extractSlice_concrete_of_code.1 var_slice_mpos var_proof_3296_offset var__proof_length var_left var_right) s₀ s₉ →
  Spec (A_fun_extractSlice var_slice_mpos var_proof_3296_offset var__proof_length var_left var_right) s₀ s₉ := by
  intro h
  simpa [A_fun_extractSlice] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
