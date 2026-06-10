import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_6355659747013642313
import generated.L1Bridgehub.L1Bridgehub.array_allocation_size_bytes
import generated.L1Bridgehub.L1Bridgehub.finalize_allocation
import generated.L1Bridgehub.L1Bridgehub.Common.if_1164150532433179709
import generated.L1Bridgehub.L1Bridgehub.mcopy

import generated.L1Bridgehub.L1Bridgehub.abi_decode_bytes_fromMemory_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common generated.L1Bridgehub L1Bridgehub

def A_abi_decode_bytes_fromMemory
    (array : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop :=
  abi_decode_bytes_fromMemory_concrete_of_code.1 array offset end_clear_sanitised_hrafn s₀ s₉

set_option maxHeartbeats 1200000 in
lemma abi_decode_bytes_fromMemory_abs_of_concrete {s₀ s₉ : State} {array offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_bytes_fromMemory_concrete_of_code.1 array offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_bytes_fromMemory array offset end_clear_sanitised_hrafn) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_bytes_fromMemory] using h

end

end generated.L1Bridgehub.L1Bridgehub
