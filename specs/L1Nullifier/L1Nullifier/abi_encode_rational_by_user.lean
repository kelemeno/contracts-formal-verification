import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.abi_encode_rational_by_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- ABI-encodes rational 1: stores literal 1 at headStart, tail = headStart + 32. -/
def A_abi_encode_rational_by (tail : Identifier) (headStart : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = (s₀🇪⟦s₀.evm.mstore headStart 1⟧)⟦tail ↦ headStart + 32⟧

set_option maxHeartbeats 800000

lemma abi_encode_rational_by_abs_of_concrete {{s₀ s₉ : State}} {tail headStart} :
  Spec (abi_encode_rational_by_concrete_of_code.1 tail headStart) s₀ s₉ →
  Spec (A_abi_encode_rational_by tail headStart) s₀ s₉ := by
  unfold abi_encode_rational_by_concrete_of_code A_abi_encode_rational_by
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMAdd', EVMMstore'] at hconcrete
  symm
  simpa using hconcrete

end

end generated.L1Nullifier.L1Nullifier
