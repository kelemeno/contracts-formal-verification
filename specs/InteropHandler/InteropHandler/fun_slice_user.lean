import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.switch_6095062188052834118
import generated.InteropHandler.InteropHandler.Common.switch_6962646901710617903
import generated.InteropHandler.InteropHandler.Common.block_7241570824081125208
import generated.InteropHandler.InteropHandler.checked_sub_uint256
import generated.InteropHandler.InteropHandler.array_allocation_size_bytes
import generated.InteropHandler.InteropHandler.finalize_allocation
import generated.InteropHandler.InteropHandler.Common.block_8890318276685480553
import generated.InteropHandler.InteropHandler.Common.block_8702072784694041670
import generated.InteropHandler.InteropHandler.mcopy
import generated.InteropHandler.InteropHandler.Common.block_4481893504431727677

import generated.InteropHandler.InteropHandler.fun_slice_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_fun_slice (var_7138_mpos : Identifier) (var_buffer_mpos var_start var_end : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_slice_abs_of_concrete {s₀ s₉ : State} {var_7138_mpos var_buffer_mpos var_start var_end} :
  Spec (fun_slice_concrete_of_code.1 var_7138_mpos var_buffer_mpos var_start var_end) s₀ s₉ →
  Spec (A_fun_slice var_7138_mpos var_buffer_mpos var_start var_end) s₀ s₉ := by
  unfold fun_slice_concrete_of_code A_fun_slice
  sorry

end

end generated.InteropHandler.InteropHandler
