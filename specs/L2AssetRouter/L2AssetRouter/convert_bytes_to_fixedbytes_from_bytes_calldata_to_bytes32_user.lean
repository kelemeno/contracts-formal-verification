import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_5915692135401846113

import generated.L2AssetRouter.L2AssetRouter.convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes32_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes32 (value : Identifier) (array len : Literal) (s₀ s₉ : State) : Prop := sorry

lemma convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes32_abs_of_concrete {s₀ s₉ : State} {value array len} :
  Spec (convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes32_concrete_of_code.1 value array len) s₀ s₉ →
  Spec (A_convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes32 value array len) s₀ s₉ := by
  unfold convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes32_concrete_of_code A_convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes32
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
