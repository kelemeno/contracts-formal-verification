import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_165571228118693302
import generated.L2AssetRouter.L2AssetRouter.Common.if_5157412582722903114

import generated.L2AssetRouter.L2AssetRouter.calldata_array_index_range_access_bytes_calldata_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_calldata_array_index_range_access_bytes_calldata (offsetOut lengthOut : Identifier) (offset length startIndex endIndex : Literal) (s₀ s₉ : State) : Prop := sorry

lemma calldata_array_index_range_access_bytes_calldata_abs_of_concrete {s₀ s₉ : State} {offsetOut lengthOut offset length startIndex endIndex} :
  Spec (calldata_array_index_range_access_bytes_calldata_concrete_of_code.1 offsetOut lengthOut offset length startIndex endIndex) s₀ s₉ →
  Spec (A_calldata_array_index_range_access_bytes_calldata offsetOut lengthOut offset length startIndex endIndex) s₀ s₉ := by
  unfold calldata_array_index_range_access_bytes_calldata_concrete_of_code A_calldata_array_index_range_access_bytes_calldata
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
