import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_6945705467323769142
import generated.L2AssetRouter.L2AssetRouter.panic_error_0x32

import generated.L2AssetRouter.L2AssetRouter.calldata_array_index_access_bytes_calldata_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_calldata_array_index_access_bytes_calldata (addr : Identifier) (base_ref length index : Literal) (s₀ s₉ : State) : Prop := sorry

lemma calldata_array_index_access_bytes_calldata_abs_of_concrete {s₀ s₉ : State} {addr base_ref length index} :
  Spec (calldata_array_index_access_bytes_calldata_concrete_of_code.1 addr base_ref length index) s₀ s₉ →
  Spec (A_calldata_array_index_access_bytes_calldata addr base_ref length index) s₀ s₉ := by
  unfold calldata_array_index_access_bytes_calldata_concrete_of_code A_calldata_array_index_access_bytes_calldata
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
