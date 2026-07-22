import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_6355659747013642313
import generated.L2InteropHandler.L2InteropHandler.Common.block_5018424720162432218
import generated.L2InteropHandler.L2InteropHandler.array_allocation_size_bytes
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation
import generated.L2InteropHandler.L2InteropHandler.Common.block_6652893194024549252
import generated.L2InteropHandler.L2InteropHandler.Common.if_1164150532433179709
import generated.L2InteropHandler.L2InteropHandler.Common.block_8316636980645894594
import generated.L2InteropHandler.L2InteropHandler.Common.block_8827457234431568735

import generated.L2InteropHandler.L2InteropHandler.abi_decode_bytes_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_abi_decode_bytes (array : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_bytes_abs_of_concrete {s₀ s₉ : State} {array offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_bytes_concrete_of_code.1 array offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_bytes array offset end_clear_sanitised_hrafn) s₀ s₉ := by
  unfold abi_decode_bytes_concrete_of_code A_abi_decode_bytes
  sorry

end

end generated.L2InteropHandler.L2InteropHandler
