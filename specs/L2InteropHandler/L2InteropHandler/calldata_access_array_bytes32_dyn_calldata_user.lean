import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_2120117105517381061
import generated.L2InteropHandler.L2InteropHandler.Common.block_5731116343986243113
import generated.L2InteropHandler.L2InteropHandler.Common.if_1209118431116190868
import generated.L2InteropHandler.L2InteropHandler.Common.if_6747681429752853338
import generated.L2InteropHandler.L2InteropHandler.Common.if_4695598817536279390

import generated.L2InteropHandler.L2InteropHandler.calldata_access_array_bytes32_dyn_calldata_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_calldata_access_array_bytes32_dyn_calldata (value length : Identifier) (base_ref ptr : Literal) (s₀ s₉ : State) : Prop := calldata_access_array_bytes32_dyn_calldata_concrete_of_code.1 value length base_ref ptr s₀ s₉

lemma calldata_access_array_bytes32_dyn_calldata_abs_of_concrete {s₀ s₉ : State} {value length base_ref ptr} :
  Spec (calldata_access_array_bytes32_dyn_calldata_concrete_of_code.1 value length base_ref ptr) s₀ s₉ →
  Spec (A_calldata_access_array_bytes32_dyn_calldata value length base_ref ptr) s₀ s₉ := by
  intro h
  simpa [A_calldata_access_array_bytes32_dyn_calldata] using h

end

end generated.L2InteropHandler.L2InteropHandler
