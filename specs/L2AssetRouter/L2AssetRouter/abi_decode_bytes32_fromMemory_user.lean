import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_5564101263465963537

import generated.L2AssetRouter.L2AssetRouter.abi_decode_bytes32_fromMemory_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_abi_decode_bytes32_fromMemory (value0 : Identifier) (headStart dataEnd : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_bytes32_fromMemory_abs_of_concrete {s₀ s₉ : State} {value0 headStart dataEnd} :
  Spec (abi_decode_bytes32_fromMemory_concrete_of_code.1 value0 headStart dataEnd) s₀ s₉ →
  Spec (A_abi_decode_bytes32_fromMemory value0 headStart dataEnd) s₀ s₉ := by
  unfold abi_decode_bytes32_fromMemory_concrete_of_code A_abi_decode_bytes32_fromMemory
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
