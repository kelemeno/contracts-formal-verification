import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_3515090449336820943

import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_payable_fromMemory_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_abi_decode_address_payable_fromMemory (value : Identifier) (offset : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_address_payable_fromMemory_abs_of_concrete {s₀ s₉ : State} {value offset} :
  Spec (abi_decode_address_payable_fromMemory_concrete_of_code.1 value offset) s₀ s₉ →
  Spec (A_abi_decode_address_payable_fromMemory value offset) s₀ s₉ := by
  unfold abi_decode_address_payable_fromMemory_concrete_of_code A_abi_decode_address_payable_fromMemory
  sorry

end

end generated.L1AssetRouter.L1AssetRouter
