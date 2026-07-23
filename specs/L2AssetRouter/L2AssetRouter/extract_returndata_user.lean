import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.switch_3088111385004876443
import generated.L2AssetRouter.L2AssetRouter.array_allocation_size_bytes
import generated.L2AssetRouter.L2AssetRouter.finalize_allocation

import generated.L2AssetRouter.L2AssetRouter.extract_returndata_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_extract_returndata (data : Identifier)  (s₀ s₉ : State) : Prop := extract_returndata_concrete_of_code.1 data s₀ s₉

lemma extract_returndata_abs_of_concrete {s₀ s₉ : State} {data } :
  Spec (extract_returndata_concrete_of_code.1 data ) s₀ s₉ →
  Spec (A_extract_returndata data ) s₀ s₉ := by
  intro h
  simpa [A_extract_returndata] using h

end

end generated.L2AssetRouter.L2AssetRouter
