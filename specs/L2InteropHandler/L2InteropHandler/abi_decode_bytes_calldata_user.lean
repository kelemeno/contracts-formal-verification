import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_6355659747013642313
import generated.L2InteropHandler.L2InteropHandler.Common.if_6747681429752853338
import generated.L2InteropHandler.L2InteropHandler.Common.if_1164150532433179709

import generated.L2InteropHandler.L2InteropHandler.abi_decode_bytes_calldata_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_abi_decode_bytes_calldata (arrayPos length : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_bytes_calldata_abs_of_concrete {s₀ s₉ : State} {arrayPos length offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_bytes_calldata_concrete_of_code.1 arrayPos length offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_bytes_calldata arrayPos length offset end_clear_sanitised_hrafn) s₀ s₉ := by
  unfold abi_decode_bytes_calldata_concrete_of_code A_abi_decode_bytes_calldata
  sorry

end

end generated.L2InteropHandler.L2InteropHandler
