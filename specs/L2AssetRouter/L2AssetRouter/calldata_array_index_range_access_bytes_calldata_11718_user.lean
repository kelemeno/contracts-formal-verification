import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_7587322151636287640

import generated.L2AssetRouter.L2AssetRouter.calldata_array_index_range_access_bytes_calldata_11718_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_calldata_array_index_range_access_bytes_calldata_11718 (offsetOut lengthOut : Identifier) (offset length : Literal) (s₀ s₉ : State) : Prop := sorry

lemma calldata_array_index_range_access_bytes_calldata_11718_abs_of_concrete {s₀ s₉ : State} {offsetOut lengthOut offset length} :
  Spec (calldata_array_index_range_access_bytes_calldata_11718_concrete_of_code.1 offsetOut lengthOut offset length) s₀ s₉ →
  Spec (A_calldata_array_index_range_access_bytes_calldata_11718 offsetOut lengthOut offset length) s₀ s₉ := by
  unfold calldata_array_index_range_access_bytes_calldata_11718_concrete_of_code A_calldata_array_index_range_access_bytes_calldata_11718
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
