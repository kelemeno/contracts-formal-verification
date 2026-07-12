import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.for_8662437257387404689

import generated.InteropHandler.InteropHandler.abi_encode_array_bytes32_dyn_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

def A_abi_encode_array_bytes32_dyn (end_clear_sanitised_hrafn : Identifier) (value pos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_array_bytes32_dyn_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn value pos} :
  Spec (abi_encode_array_bytes32_dyn_concrete_of_code.1 end_clear_sanitised_hrafn value pos) s₀ s₉ →
  Spec (A_abi_encode_array_bytes32_dyn end_clear_sanitised_hrafn value pos) s₀ s₉ := by
  unfold abi_encode_array_bytes32_dyn_concrete_of_code A_abi_encode_array_bytes32_dyn
  sorry

end

end generated.InteropHandler.InteropHandler
