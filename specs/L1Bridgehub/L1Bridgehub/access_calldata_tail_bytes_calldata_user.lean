import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_1209118431116190868
import generated.L1Bridgehub.L1Bridgehub.Common.if_6747681429752853338
import generated.L1Bridgehub.L1Bridgehub.Common.if_8274955638413537848

import generated.L1Bridgehub.L1Bridgehub.access_calldata_tail_bytes_calldata_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common 

def A_access_calldata_tail_bytes_calldata (addr length : Identifier) (base_ref ptr_to_tail : Literal) (s₀ s₉ : State) : Prop := access_calldata_tail_bytes_calldata_concrete_of_code.1 addr length base_ref ptr_to_tail s₀ s₉

lemma access_calldata_tail_bytes_calldata_abs_of_concrete {s₀ s₉ : State} {addr length base_ref ptr_to_tail} :
  Spec (access_calldata_tail_bytes_calldata_concrete_of_code.1 addr length base_ref ptr_to_tail) s₀ s₉ →
  Spec (A_access_calldata_tail_bytes_calldata addr length base_ref ptr_to_tail) s₀ s₉ := by
  intro h
  simpa [A_access_calldata_tail_bytes_calldata] using h

end

end generated.L1Bridgehub.L1Bridgehub
