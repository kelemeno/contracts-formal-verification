import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.for_7291460318072256587
import generated.L2InteropHandler.L2InteropHandler.memory_array_index_access_enum_CallStatus_dyn
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation
import generated.L2InteropHandler.L2InteropHandler.fun_formatEvmV1
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes32_bytes_bytes

import generated.L2InteropHandler.L2InteropHandler.fun_executeCalls_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_fun_executeCalls  (var_sourceChainId var_bundleHash var__interopBundle_mpos var_providedCallStatus_mpos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_executeCalls_abs_of_concrete {s₀ s₉ : State} { var_sourceChainId var_bundleHash var__interopBundle_mpos var_providedCallStatus_mpos} :
  Spec (fun_executeCalls_concrete_of_code.1  var_sourceChainId var_bundleHash var__interopBundle_mpos var_providedCallStatus_mpos) s₀ s₉ →
  Spec (A_fun_executeCalls  var_sourceChainId var_bundleHash var__interopBundle_mpos var_providedCallStatus_mpos) s₀ s₉ := by
  unfold fun_executeCalls_concrete_of_code A_fun_executeCalls
  sorry

end

end generated.L2InteropHandler.L2InteropHandler
