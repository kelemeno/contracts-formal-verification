import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_7669879635616097659
import generated.L1Bridgehub.L1Bridgehub.Common.if_3680740834951988335
import generated.L1Bridgehub.L1Bridgehub.Common.if_4112092877758689662

import generated.L1Bridgehub.L1Bridgehub.abi_decode_struct_L2TransactionRequestTwoBridgesOuter_calldata_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common 

def A_abi_decode_struct_L2TransactionRequestTwoBridgesOuter_calldata (value0 : Identifier) (dataEnd : Literal) (s₀ s₉ : State) : Prop :=
  abi_decode_struct_L2TransactionRequestTwoBridgesOuter_calldata_concrete_of_code.1 value0 dataEnd s₀ s₉

lemma abi_decode_struct_L2TransactionRequestTwoBridgesOuter_calldata_abs_of_concrete {s₀ s₉ : State} {value0 dataEnd} :
  Spec (abi_decode_struct_L2TransactionRequestTwoBridgesOuter_calldata_concrete_of_code.1 value0 dataEnd) s₀ s₉ →
  Spec (A_abi_decode_struct_L2TransactionRequestTwoBridgesOuter_calldata value0 dataEnd) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_struct_L2TransactionRequestTwoBridgesOuter_calldata] using h

end

end generated.L1Bridgehub.L1Bridgehub
