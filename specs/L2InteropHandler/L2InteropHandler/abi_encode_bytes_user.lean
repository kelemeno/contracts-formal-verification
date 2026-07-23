import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_1972314688047089626
import generated.L2InteropHandler.L2InteropHandler.mcopy
import generated.L2InteropHandler.L2InteropHandler.Common.block_6443795390729041228
import generated.L2InteropHandler.L2InteropHandler.Common.block_8835311816514709948

import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_abi_encode_bytes (end_clear_sanitised_hrafn : Identifier) (value pos : Literal) (s₀ s₉ : State) : Prop := abi_encode_bytes_concrete_of_code.1 end_clear_sanitised_hrafn value pos s₀ s₉

lemma abi_encode_bytes_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn value pos} :
  Spec (abi_encode_bytes_concrete_of_code.1 end_clear_sanitised_hrafn value pos) s₀ s₉ →
  Spec (A_abi_encode_bytes end_clear_sanitised_hrafn value pos) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_bytes] using h

end

end generated.L2InteropHandler.L2InteropHandler
