import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_6040632739308624336

import generated.L1AssetRouter.L1AssetRouter.abi_encode_array_bytes32_dyn_calldata_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_abi_encode_array_bytes32_dyn_calldata (end_clear_sanitised_hrafn : Identifier) (start length pos : Literal) (s₀ s₉ : State) : Prop :=
  abi_encode_array_bytes32_dyn_calldata_concrete_of_code.1 end_clear_sanitised_hrafn start length pos s₀ s₉

lemma abi_encode_array_bytes32_dyn_calldata_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn start length pos} :
  Spec (abi_encode_array_bytes32_dyn_calldata_concrete_of_code.1 end_clear_sanitised_hrafn start length pos) s₀ s₉ →
  Spec (A_abi_encode_array_bytes32_dyn_calldata end_clear_sanitised_hrafn start length pos) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_array_bytes32_dyn_calldata] using h

end

end generated.L1AssetRouter.L1AssetRouter
