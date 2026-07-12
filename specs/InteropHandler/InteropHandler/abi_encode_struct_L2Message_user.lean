import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_1611197801715198094
import generated.InteropHandler.InteropHandler.Common.block_6920406222900660738
import generated.InteropHandler.InteropHandler.Common.block_2939661267400252911
import generated.InteropHandler.InteropHandler.Common.block_648524209478556713
import generated.InteropHandler.InteropHandler.abi_encode_bytes

import generated.InteropHandler.InteropHandler.abi_encode_struct_L2Message_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_abi_encode_struct_L2Message (end_clear_sanitised_hrafn : Identifier) (value pos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_struct_L2Message_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn value pos} :
  Spec (abi_encode_struct_L2Message_concrete_of_code.1 end_clear_sanitised_hrafn value pos) s₀ s₉ →
  Spec (A_abi_encode_struct_L2Message end_clear_sanitised_hrafn value pos) s₀ s₉ := by
  unfold abi_encode_struct_L2Message_concrete_of_code A_abi_encode_struct_L2Message
  sorry

end

end generated.InteropHandler.InteropHandler
