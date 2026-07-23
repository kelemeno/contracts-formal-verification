import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_8636398813138732111
import generated.L2AssetRouter.L2AssetRouter.Common.block_3929849630842800116
import generated.L2AssetRouter.L2AssetRouter.Common.block_2860610078672225083

import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes_calldata_to_bytes_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_abi_encode_bytes_calldata_to_bytes (end_clear_sanitised_hrafn : Identifier) (start length pos : Literal) (s₀ s₉ : State) : Prop := abi_encode_bytes_calldata_to_bytes_concrete_of_code.1 end_clear_sanitised_hrafn start length pos s₀ s₉

lemma abi_encode_bytes_calldata_to_bytes_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn start length pos} :
  Spec (abi_encode_bytes_calldata_to_bytes_concrete_of_code.1 end_clear_sanitised_hrafn start length pos) s₀ s₉ →
  Spec (A_abi_encode_bytes_calldata_to_bytes end_clear_sanitised_hrafn start length pos) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_bytes_calldata_to_bytes] using h

end

end generated.L2AssetRouter.L2AssetRouter
