import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_8636398813138732111
import generated.InteropHandler.InteropHandler.Common.block_3929849630842800116
import generated.InteropHandler.InteropHandler.Common.block_2860610078672225083

import generated.InteropHandler.InteropHandler.abi_encode_bytes_calldata_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

def A_abi_encode_bytes_calldata (end_clear_sanitised_hrafn : Identifier) (start length pos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_bytes_calldata_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn start length pos} :
  Spec (abi_encode_bytes_calldata_concrete_of_code.1 end_clear_sanitised_hrafn start length pos) s₀ s₉ →
  Spec (A_abi_encode_bytes_calldata end_clear_sanitised_hrafn start length pos) s₀ s₉ := by
  unfold abi_encode_bytes_calldata_concrete_of_code A_abi_encode_bytes_calldata
  sorry

end

end generated.InteropHandler.InteropHandler
