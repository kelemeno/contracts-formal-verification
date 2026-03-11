import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes

import generated.L1AssetRouter.L1AssetRouter.Common.for_6252067074600046020

import generated.L1AssetRouter.L1AssetRouter.abi_encode_array_bytes_dyn_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_abi_encode_array_bytes_dyn (end_clear_sanitised_hrafn : Identifier) (value pos : Literal) (s₀ s₉ : State) : Prop :=
  abi_encode_array_bytes_dyn_concrete_of_code.1 end_clear_sanitised_hrafn value pos s₀ s₉

lemma abi_encode_array_bytes_dyn_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn value pos} :
  Spec (abi_encode_array_bytes_dyn_concrete_of_code.1 end_clear_sanitised_hrafn value pos) s₀ s₉ →
  Spec (A_abi_encode_array_bytes_dyn end_clear_sanitised_hrafn value pos) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_array_bytes_dyn] using h

end

end generated.L1AssetRouter.L1AssetRouter
