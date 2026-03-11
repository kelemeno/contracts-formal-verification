import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR is 0x800A = 32778 (system contract address on L2). -/
def A_constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR (ret : Identifier) (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦ret ↦ 32778⟧

set_option maxHeartbeats 800000

lemma constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR_abs_of_concrete {s₀ s₉ : State} {ret} :
  Spec (constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR_concrete_of_code.1 ret) s₀ s₉ →
  Spec (A_constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR ret) s₀ s₉ := by
  unfold constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR_concrete_of_code A_constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  symm
  convert hconcrete using 2
  simp [lookup_insert']

end

end generated.L1Nullifier.L1Nullifier
