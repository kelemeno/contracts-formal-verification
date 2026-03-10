import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR (ret : Identifier)  (s₀ s₉ : State) : Prop := True

lemma constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR_abs_of_concrete {s₀ s₉ : State} {ret } :
  Spec (constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR_concrete_of_code.1 ret) s₀ s₉ →
  Spec (A_constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR ret) s₀ s₉ := by
  unfold A_constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
