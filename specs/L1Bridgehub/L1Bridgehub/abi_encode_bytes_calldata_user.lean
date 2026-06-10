import Clear.ReasoningPrinciple


import generated.L1Bridgehub.L1Bridgehub.abi_encode_bytes_calldata_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_bytes_calldata (end_clear_sanitised_hrafn : Identifier) (start length pos : Literal) (s₀ s₉ : State) : Prop :=
  abi_encode_bytes_calldata_concrete_of_code.1 end_clear_sanitised_hrafn start length pos s₀ s₉

lemma abi_encode_bytes_calldata_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn start length pos} :
  Spec (abi_encode_bytes_calldata_concrete_of_code.1 end_clear_sanitised_hrafn start length pos) s₀ s₉ →
  Spec (A_abi_encode_bytes_calldata end_clear_sanitised_hrafn start length pos) s₀ s₉ := by
  unfold A_abi_encode_bytes_calldata
  simpa [abi_encode_bytes_calldata_concrete_of_code]

end

end generated.L1Bridgehub.L1Bridgehub
