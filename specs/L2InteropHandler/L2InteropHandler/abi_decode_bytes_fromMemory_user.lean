import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_6355659747013642313
import generated.L2InteropHandler.L2InteropHandler.Common.block_3705893829594021408
import generated.L2InteropHandler.L2InteropHandler.array_allocation_size_bytes
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation
import generated.L2InteropHandler.L2InteropHandler.Common.block_6652893194024549252
import generated.L2InteropHandler.L2InteropHandler.Common.if_1164150532433179709
import generated.L2InteropHandler.L2InteropHandler.Common.block_219791391107394072
import generated.L2InteropHandler.L2InteropHandler.mcopy
import generated.L2InteropHandler.L2InteropHandler.Common.block_8827457234431568735

import generated.L2InteropHandler.L2InteropHandler.abi_decode_bytes_fromMemory_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_abi_decode_bytes_fromMemory (array : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := abi_decode_bytes_fromMemory_concrete_of_code.1 array offset end_clear_sanitised_hrafn s₀ s₉

lemma abi_decode_bytes_fromMemory_abs_of_concrete {s₀ s₉ : State} {array offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_bytes_fromMemory_concrete_of_code.1 array offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_bytes_fromMemory array offset end_clear_sanitised_hrafn) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_bytes_fromMemory] using h

end

end generated.L2InteropHandler.L2InteropHandler
