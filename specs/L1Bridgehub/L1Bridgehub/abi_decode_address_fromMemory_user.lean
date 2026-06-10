import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_3128629598900990522

import generated.L1Bridgehub.L1Bridgehub.abi_decode_address_fromMemory_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common 

def A_abi_decode_address_fromMemory
    (value : Identifier) (offset : Literal) (s₀ s₉ : State) : Prop :=
  abi_decode_address_fromMemory_concrete_of_code.1 value offset s₀ s₉

lemma abi_decode_address_fromMemory_abs_of_concrete {s₀ s₉ : State} {value offset} :
  Spec (abi_decode_address_fromMemory_concrete_of_code.1 value offset) s₀ s₉ →
  Spec (A_abi_decode_address_fromMemory value offset) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_address_fromMemory] using h

end

end generated.L1Bridgehub.L1Bridgehub
