import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.switch_6095062188052834118
import generated.L2InteropHandler.L2InteropHandler.Common.switch_6962646901710617903
import generated.L2InteropHandler.L2InteropHandler.Common.block_7241570824081125208
import generated.L2InteropHandler.L2InteropHandler.checked_sub_uint256
import generated.L2InteropHandler.L2InteropHandler.array_allocation_size_bytes
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation
import generated.L2InteropHandler.L2InteropHandler.Common.block_8890318276685480553
import generated.L2InteropHandler.L2InteropHandler.Common.block_8702072784694041670
import generated.L2InteropHandler.L2InteropHandler.mcopy
import generated.L2InteropHandler.L2InteropHandler.Common.block_644093042151948039

import generated.L2InteropHandler.L2InteropHandler.fun_slice_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_fun_slice (var__mpos : Identifier) (var_buffer_mpos var_start var_end : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_slice_abs_of_concrete {s₀ s₉ : State} {var__mpos var_buffer_mpos var_start var_end} :
  Spec (fun_slice_concrete_of_code.1 var__mpos var_buffer_mpos var_start var_end) s₀ s₉ →
  Spec (A_fun_slice var__mpos var_buffer_mpos var_start var_end) s₀ s₉ := by
  unfold fun_slice_concrete_of_code A_fun_slice
  sorry

end

end generated.L2InteropHandler.L2InteropHandler
