import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_bytes

import generated.L1Nullifier.L1Nullifier.abi_encode_address_bytes32_bytes_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_abi_encode_address_bytes32_bytes (tail : Identifier) (headStart value0 value1 value2 : Literal) (s₀ s₉ : State) : Prop :=
  abi_encode_address_bytes32_bytes_concrete_of_code.1 tail headStart value0 value1 value2 s₀ s₉

lemma abi_encode_address_bytes32_bytes_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2} :
  Spec (abi_encode_address_bytes32_bytes_concrete_of_code.1 tail headStart value0 value1 value2) s₀ s₉ →
  Spec (A_abi_encode_address_bytes32_bytes tail headStart value0 value1 value2) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_address_bytes32_bytes] using h

end

end generated.L1Nullifier.L1Nullifier
