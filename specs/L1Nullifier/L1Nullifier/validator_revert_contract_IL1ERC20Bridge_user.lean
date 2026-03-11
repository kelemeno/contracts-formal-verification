import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.validator_revert_contract_IL1ERC20Bridge_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_validator_revert_contract_IL1ERC20Bridge  (value : Literal) (s₀ s₉ : State) : Prop := True

lemma validator_revert_contract_IL1ERC20Bridge_abs_of_concrete {s₀ s₉ : State} { value} :
  Spec (validator_revert_contract_IL1ERC20Bridge_concrete_of_code.1 value) s₀ s₉ →
  Spec (A_validator_revert_contract_IL1ERC20Bridge value) s₀ s₉ := by
  unfold A_validator_revert_contract_IL1ERC20Bridge
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
