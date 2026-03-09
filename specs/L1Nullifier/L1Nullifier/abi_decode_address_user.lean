import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.validator_revert_contract_IL1ERC20Bridge

import generated.L1Nullifier.L1Nullifier.abi_decode_address_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_abi_decode_address (value : Identifier) (offset : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_address_abs_of_concrete {s₀ s₉ : State} {value offset} :
  Spec (abi_decode_address_concrete_of_code.1 value offset) s₀ s₉ →
  Spec (A_abi_decode_address value offset) s₀ s₉ := by
  unfold abi_decode_address_concrete_of_code A_abi_decode_address
  sorry

end

end generated.L1Nullifier.L1Nullifier
