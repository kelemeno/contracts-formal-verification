import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes_calldata_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- ABI-encodes a bytes value from calldata:
    - stores length at pos
    - calldatacopy length bytes from calldata[start] to memory[pos+32]
    - zero-pads at pos+length+32
    - end = pos + round32(length) + 32 -/
def abi_encode_bytes_calldata_evm (evm : EVM) (start length pos : Literal) : EVM :=
  ((evm.mstore pos length).calldatacopy (pos + 32) start length).mstore (pos + length + 32) 0

def A_abi_encode_bytes_calldata (end_clear_sanitised_hrafn : Identifier) (start length pos : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = (s₀🇪⟦abi_encode_bytes_calldata_evm s₀.evm start length pos⟧)⟦end_clear_sanitised_hrafn ↦ pos + Fin.land (length + 31) (UInt256.lnot 31) + 32⟧

set_option maxHeartbeats 800000

lemma abi_encode_bytes_calldata_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn start length pos} :
  Spec (abi_encode_bytes_calldata_concrete_of_code.1 end_clear_sanitised_hrafn start length pos) s₀ s₉ →
  Spec (A_abi_encode_bytes_calldata end_clear_sanitised_hrafn start length pos) s₀ s₉ := by
  unfold abi_encode_bytes_calldata_concrete_of_code A_abi_encode_bytes_calldata
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  symm
  simpa [abi_encode_bytes_calldata_evm] using hconcrete

end

end generated.L1AssetRouter.L1AssetRouter
