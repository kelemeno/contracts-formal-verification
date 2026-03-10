import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes_calldata_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_bytes_calldata (end_clear_sanitised_hrafn : Identifier) (start length pos : Literal) (s₀ s₉ : State) : Prop := True

lemma abi_encode_bytes_calldata_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn start length pos} :
  Spec (abi_encode_bytes_calldata_concrete_of_code.1 end_clear_sanitised_hrafn start length pos) s₀ s₉ →
  Spec (A_abi_encode_bytes_calldata end_clear_sanitised_hrafn start length pos) s₀ s₉ := by
  unfold abi_encode_bytes_calldata_concrete_of_code A_abi_encode_bytes_calldata
  unfold A_abi_encode_bytes_calldata
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1AssetRouter.L1AssetRouter
