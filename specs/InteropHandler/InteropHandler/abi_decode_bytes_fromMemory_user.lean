import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_6355659747013642313
import generated.InteropHandler.InteropHandler.Common.block_3705893829594021408
import generated.InteropHandler.InteropHandler.array_allocation_size_bytes
import generated.InteropHandler.InteropHandler.finalize_allocation
import generated.InteropHandler.InteropHandler.Common.block_6652893194024549252
import generated.InteropHandler.InteropHandler.Common.if_1164150532433179709
import generated.InteropHandler.InteropHandler.Common.block_219791391107394072
import generated.InteropHandler.InteropHandler.mcopy
import generated.InteropHandler.InteropHandler.Common.block_8827457234431568735

import generated.InteropHandler.InteropHandler.abi_decode_bytes_fromMemory_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_abi_decode_bytes_fromMemory (array : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_bytes_fromMemory_abs_of_concrete {s₀ s₉ : State} {array offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_bytes_fromMemory_concrete_of_code.1 array offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_bytes_fromMemory array offset end_clear_sanitised_hrafn) s₀ s₉ := by
  unfold abi_decode_bytes_fromMemory_concrete_of_code A_abi_decode_bytes_fromMemory
  sorry

end

end generated.InteropHandler.InteropHandler
