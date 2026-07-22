import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes_calldata_to_bytes

import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes_calldata_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_abi_encode_bytes_calldata (tail : Identifier) (headStart value0 value1 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_bytes_calldata_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1} :
  Spec (abi_encode_bytes_calldata_concrete_of_code.1 tail headStart value0 value1) s₀ s₉ →
  Spec (A_abi_encode_bytes_calldata tail headStart value0 value1) s₀ s₉ := by
  unfold abi_encode_bytes_calldata_concrete_of_code A_abi_encode_bytes_calldata
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
