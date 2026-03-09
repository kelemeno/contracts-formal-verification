import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_uint256_address_address_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def addressMask : UInt256 := Fin.shiftLeft 1 160 - 1

def abi_encode_uint256_address_address_evm (evm : EVM) (headStart value0 value1 value2 : Literal) : EVM :=
  (((evm.mstore headStart value0).mstore (headStart + 32) (Fin.land value1 addressMask)).mstore (headStart + 64) (Fin.land value2 addressMask))

def A_abi_encode_uint256_address_address (tail : Identifier) (headStart value0 value1 value2 : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = (s₀🇪⟦abi_encode_uint256_address_address_evm s₀.evm headStart value0 value1 value2⟧)⟦tail ↦ headStart + 96⟧

lemma abi_encode_uint256_address_address_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2} :
  Spec (abi_encode_uint256_address_address_concrete_of_code.1 tail headStart value0 value1 value2) s₀ s₉ →
  Spec (A_abi_encode_uint256_address_address tail headStart value0 value1 value2) s₀ s₉ := by
  unfold abi_encode_uint256_address_address_concrete_of_code A_abi_encode_uint256_address_address
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  symm
  simpa [abi_encode_uint256_address_address_evm, addressMask] using hconcrete

end

end generated.L1AssetRouter.L1AssetRouter
