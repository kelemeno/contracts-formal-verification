import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_1292814770935828014
import generated.InteropHandler.InteropHandler.Common.block_1556246446440514414
import generated.InteropHandler.InteropHandler.Common.block_656024305002698689
import generated.InteropHandler.InteropHandler.Common.for_4476381376322263891
import generated.InteropHandler.InteropHandler.Common.block_3555877409875952246
import generated.InteropHandler.InteropHandler.Common.block_2574327109930815523
import generated.InteropHandler.InteropHandler.finalize_allocation
import generated.InteropHandler.InteropHandler.Common.block_6979264426086026670
import generated.InteropHandler.InteropHandler.Common.block_4597829123177901218
import generated.InteropHandler.InteropHandler.Common.for_8649674080430825952
import generated.InteropHandler.InteropHandler.memory_array_index_access_enum_CallStatus_dyn
import generated.InteropHandler.InteropHandler.fun_formatEvmV1
import generated.InteropHandler.InteropHandler.abi_encode_bytes32_bytes_bytes

import generated.InteropHandler.InteropHandler.fun_markFullyExecutedAndRun_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_fun_markFullyExecutedAndRun  (var_bundleHash var_interopBundle_mpos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_markFullyExecutedAndRun_abs_of_concrete {s₀ s₉ : State} { var_bundleHash var_interopBundle_mpos} :
  Spec (fun_markFullyExecutedAndRun_concrete_of_code.1  var_bundleHash var_interopBundle_mpos) s₀ s₉ →
  Spec (A_fun_markFullyExecutedAndRun  var_bundleHash var_interopBundle_mpos) s₀ s₉ := by
  unfold fun_markFullyExecutedAndRun_concrete_of_code A_fun_markFullyExecutedAndRun
  sorry

end

end generated.InteropHandler.InteropHandler
