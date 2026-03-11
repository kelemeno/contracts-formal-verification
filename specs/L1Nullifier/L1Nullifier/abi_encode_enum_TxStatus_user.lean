import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.panic_error_0x21

import generated.L1Nullifier.L1Nullifier.abi_encode_enum_TxStatus_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_abi_encode_enum_TxStatus  (value pos : Literal) (s₀ s₉ : State) : Prop := True

lemma abi_encode_enum_TxStatus_abs_of_concrete {s₀ s₉ : State} { value pos} :
  Spec (abi_encode_enum_TxStatus_concrete_of_code.1 value pos) s₀ s₉ →
  Spec (A_abi_encode_enum_TxStatus value pos) s₀ s₉ := by
  unfold A_abi_encode_enum_TxStatus
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
