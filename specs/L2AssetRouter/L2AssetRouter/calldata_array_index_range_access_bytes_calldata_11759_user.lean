import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_4923613851667228793
import generated.L2AssetRouter.L2AssetRouter.Common.if_5157412582722903114

import generated.L2AssetRouter.L2AssetRouter.calldata_array_index_range_access_bytes_calldata_11759_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_calldata_array_index_range_access_bytes_calldata_11759 (offsetOut lengthOut : Identifier) (offset length endIndex : Literal) (s₀ s₉ : State) : Prop := calldata_array_index_range_access_bytes_calldata_11759_concrete_of_code.1 offsetOut lengthOut offset length endIndex s₀ s₉

lemma calldata_array_index_range_access_bytes_calldata_11759_abs_of_concrete {s₀ s₉ : State} {offsetOut lengthOut offset length endIndex} :
  Spec (calldata_array_index_range_access_bytes_calldata_11759_concrete_of_code.1 offsetOut lengthOut offset length endIndex) s₀ s₉ →
  Spec (A_calldata_array_index_range_access_bytes_calldata_11759 offsetOut lengthOut offset length endIndex) s₀ s₉ := by
  intro h
  simpa [A_calldata_array_index_range_access_bytes_calldata_11759] using h

end

end generated.L2AssetRouter.L2AssetRouter
