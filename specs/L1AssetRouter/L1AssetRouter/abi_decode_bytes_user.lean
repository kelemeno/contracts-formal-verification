import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_7928665324398554026
import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_5631566510356250141

import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_abi_decode_bytes (array : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_bytes_abs_of_concrete {s₀ s₉ : State} {array offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_bytes_concrete_of_code.1 array offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_bytes array offset end_clear_sanitised_hrafn) s₀ s₉ := by
  unfold abi_decode_bytes_concrete_of_code A_abi_decode_bytes
  sorry

end

end generated.L1AssetRouter.L1AssetRouter
