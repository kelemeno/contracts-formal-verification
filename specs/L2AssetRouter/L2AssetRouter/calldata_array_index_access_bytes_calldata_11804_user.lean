import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_4669985319712420221
import generated.L2AssetRouter.L2AssetRouter.panic_error_0x32

import generated.L2AssetRouter.L2AssetRouter.calldata_array_index_access_bytes_calldata_11804_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_calldata_array_index_access_bytes_calldata_11804 (addr : Identifier) (base_ref length : Literal) (s₀ s₉ : State) : Prop := sorry

lemma calldata_array_index_access_bytes_calldata_11804_abs_of_concrete {s₀ s₉ : State} {addr base_ref length} :
  Spec (calldata_array_index_access_bytes_calldata_11804_concrete_of_code.1 addr base_ref length) s₀ s₉ →
  Spec (A_calldata_array_index_access_bytes_calldata_11804 addr base_ref length) s₀ s₉ := by
  unfold calldata_array_index_access_bytes_calldata_11804_concrete_of_code A_calldata_array_index_access_bytes_calldata_11804
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
