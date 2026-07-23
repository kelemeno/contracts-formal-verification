import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_8636398813138732111
import generated.L2InteropHandler.L2InteropHandler.Common.block_3929849630842800116
import generated.L2InteropHandler.L2InteropHandler.Common.block_2860610078672225083

import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes_calldata_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_abi_encode_bytes_calldata (end_clear_sanitised_hrafn : Identifier) (start length pos : Literal) (s₀ s₉ : State) : Prop := abi_encode_bytes_calldata_concrete_of_code.1 end_clear_sanitised_hrafn start length pos s₀ s₉

lemma abi_encode_bytes_calldata_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn start length pos} :
  Spec (abi_encode_bytes_calldata_concrete_of_code.1 end_clear_sanitised_hrafn start length pos) s₀ s₉ →
  Spec (A_abi_encode_bytes_calldata end_clear_sanitised_hrafn start length pos) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_bytes_calldata] using h

end

end generated.L2InteropHandler.L2InteropHandler
