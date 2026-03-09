import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_7502148099353757069

import generated.L1Nullifier.L1Nullifier.abi_decode_enum_TxStatus_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_abi_decode_enum_TxStatus (value : Identifier) (offset : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_enum_TxStatus_abs_of_concrete {s₀ s₉ : State} {value offset} :
  Spec (abi_decode_enum_TxStatus_concrete_of_code.1 value offset) s₀ s₉ →
  Spec (A_abi_decode_enum_TxStatus value offset) s₀ s₉ := by
  unfold abi_decode_enum_TxStatus_concrete_of_code A_abi_decode_enum_TxStatus
  sorry

end

end generated.L1Nullifier.L1Nullifier
