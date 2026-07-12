import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_2014493949976689796

import generated.InteropHandler.InteropHandler.abi_encode_enum_CallStatus_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

def A_abi_encode_enum_CallStatus  (value pos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_enum_CallStatus_abs_of_concrete {s₀ s₉ : State} { value pos} :
  Spec (abi_encode_enum_CallStatus_concrete_of_code.1  value pos) s₀ s₉ →
  Spec (A_abi_encode_enum_CallStatus  value pos) s₀ s₉ := by
  unfold abi_encode_enum_CallStatus_concrete_of_code A_abi_encode_enum_CallStatus
  sorry

end

end generated.InteropHandler.InteropHandler
