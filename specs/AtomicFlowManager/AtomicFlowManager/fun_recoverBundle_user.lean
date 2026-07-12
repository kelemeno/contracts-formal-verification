import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6530031529764029836
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_997145437097312209
import generated.AtomicFlowManager.AtomicFlowManager.Common.for_7993347358814374560
import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.cleanup_address
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_bytes
import generated.AtomicFlowManager.AtomicFlowManager.revert_forward
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bool_fromMemory
import generated.AtomicFlowManager.AtomicFlowManager.increment_uint256
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1810053395204506171
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_uint256_7396

import generated.AtomicFlowManager.AtomicFlowManager.fun_recoverBundle_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_fun_recoverBundle  (var__flowId var_bundleHash var_bundle_mpos : Literal) (s₀ s₉ : State) : Prop := fun_recoverBundle_concrete_of_code.1  var__flowId var_bundleHash var_bundle_mpos s₀ s₉

lemma fun_recoverBundle_abs_of_concrete {s₀ s₉ : State} { var__flowId var_bundleHash var_bundle_mpos} :
  Spec (fun_recoverBundle_concrete_of_code.1  var__flowId var_bundleHash var_bundle_mpos) s₀ s₉ →
  Spec (A_fun_recoverBundle  var__flowId var_bundleHash var_bundle_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_recoverBundle] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
