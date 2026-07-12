import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_6355659747013642313
import generated.InteropHandler.InteropHandler.Common.block_5018424720162432218
import generated.InteropHandler.InteropHandler.array_allocation_size_bytes
import generated.InteropHandler.InteropHandler.finalize_allocation
import generated.InteropHandler.InteropHandler.Common.block_6652893194024549252
import generated.InteropHandler.InteropHandler.Common.if_1164150532433179709
import generated.InteropHandler.InteropHandler.Common.block_8316636980645894594
import generated.InteropHandler.InteropHandler.Common.block_8827457234431568735

import generated.InteropHandler.InteropHandler.abi_decode_bytes_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_abi_decode_bytes (array : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_bytes_abs_of_concrete {s₀ s₉ : State} {array offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_bytes_concrete_of_code.1 array offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_bytes array offset end_clear_sanitised_hrafn) s₀ s₉ := by
  unfold abi_decode_bytes_concrete_of_code A_abi_decode_bytes
  sorry

end

end generated.InteropHandler.InteropHandler
