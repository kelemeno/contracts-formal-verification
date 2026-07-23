import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_1611197801715198094
import generated.L2InteropHandler.L2InteropHandler.Common.block_6920406222900660738
import generated.L2InteropHandler.L2InteropHandler.Common.block_2939661267400252911
import generated.L2InteropHandler.L2InteropHandler.Common.block_648524209478556713
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes

import generated.L2InteropHandler.L2InteropHandler.abi_encode_struct_L2Message_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_abi_encode_struct_L2Message (end_clear_sanitised_hrafn : Identifier) (value pos : Literal) (s₀ s₉ : State) : Prop := abi_encode_struct_L2Message_concrete_of_code.1 end_clear_sanitised_hrafn value pos s₀ s₉

lemma abi_encode_struct_L2Message_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn value pos} :
  Spec (abi_encode_struct_L2Message_concrete_of_code.1 end_clear_sanitised_hrafn value pos) s₀ s₉ →
  Spec (A_abi_encode_struct_L2Message end_clear_sanitised_hrafn value pos) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_struct_L2Message] using h

end

end generated.L2InteropHandler.L2InteropHandler
