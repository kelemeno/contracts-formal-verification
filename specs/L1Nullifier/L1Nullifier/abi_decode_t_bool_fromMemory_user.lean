import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_6413955827503143329

import generated.L1Nullifier.L1Nullifier.abi_decode_t_bool_fromMemory_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_abi_decode_t_bool_fromMemory (value : Identifier) (offset : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_t_bool_fromMemory_abs_of_concrete {s₀ s₉ : State} {value offset} :
  Spec (abi_decode_t_bool_fromMemory_concrete_of_code.1 value offset) s₀ s₉ →
  Spec (A_abi_decode_t_bool_fromMemory value offset) s₀ s₉ := by
  unfold abi_decode_t_bool_fromMemory_concrete_of_code A_abi_decode_t_bool_fromMemory
  sorry

end

end generated.L1Nullifier.L1Nullifier
