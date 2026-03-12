import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.panic_error_0x21

import generated.L1Nullifier.L1Nullifier.validator_assert_enum_TxStatus_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_validator_assert_enum_TxStatus  (value : Literal) (s₀ s₉ : State) : Prop :=
  validator_assert_enum_TxStatus_concrete_of_code.1 value s₀ s₉

lemma validator_assert_enum_TxStatus_abs_of_concrete {s₀ s₉ : State} { value} :
  Spec (validator_assert_enum_TxStatus_concrete_of_code.1 value) s₀ s₉ →
  Spec (A_validator_assert_enum_TxStatus value) s₀ s₉ := by
  intro h
  simpa [A_validator_assert_enum_TxStatus] using h

end

end generated.L1Nullifier.L1Nullifier
