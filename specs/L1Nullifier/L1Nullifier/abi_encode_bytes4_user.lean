import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.abi_encode_bytes4_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- ABI-encodes a bytes4: stores value0 masked to top 32 bits at offset 4, tail = 36. -/
def A_abi_encode_bytes4 (tail : Identifier) (value0 : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = (s₀🇪⟦s₀.evm.mstore 4 (Fin.land value0 (Fin.shiftLeft 4294967295 224))⟧)⟦tail ↦ 36⟧

set_option maxHeartbeats 800000

lemma abi_encode_bytes4_abs_of_concrete {{s₀ s₉ : State}} {tail value0} :
  Spec (abi_encode_bytes4_concrete_of_code.1 tail value0) s₀ s₉ →
  Spec (A_abi_encode_bytes4 tail value0) s₀ s₉ := by
  unfold abi_encode_bytes4_concrete_of_code A_abi_encode_bytes4
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMShl', EVMAnd', EVMMstore'] at hconcrete
  symm
  simpa using hconcrete

end

end generated.L1Nullifier.L1Nullifier
