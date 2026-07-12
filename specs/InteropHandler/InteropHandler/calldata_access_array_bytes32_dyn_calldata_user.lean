import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_2120117105517381061
import generated.InteropHandler.InteropHandler.Common.block_5731116343986243113
import generated.InteropHandler.InteropHandler.Common.if_1209118431116190868
import generated.InteropHandler.InteropHandler.Common.if_6747681429752853338
import generated.InteropHandler.InteropHandler.Common.if_4695598817536279390

import generated.InteropHandler.InteropHandler.calldata_access_array_bytes32_dyn_calldata_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

def A_calldata_access_array_bytes32_dyn_calldata (value length : Identifier) (base_ref ptr : Literal) (s₀ s₉ : State) : Prop := sorry

lemma calldata_access_array_bytes32_dyn_calldata_abs_of_concrete {s₀ s₉ : State} {value length base_ref ptr} :
  Spec (calldata_access_array_bytes32_dyn_calldata_concrete_of_code.1 value length base_ref ptr) s₀ s₉ →
  Spec (A_calldata_access_array_bytes32_dyn_calldata value length base_ref ptr) s₀ s₉ := by
  unfold calldata_access_array_bytes32_dyn_calldata_concrete_of_code A_calldata_access_array_bytes32_dyn_calldata
  sorry

end

end generated.InteropHandler.InteropHandler
