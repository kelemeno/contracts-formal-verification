import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_1209118431116190868
import generated.L1Bridgehub.L1Bridgehub.Common.if_6747681429752853338
import generated.L1Bridgehub.L1Bridgehub.Common.if_1054195021732265141

import generated.L1Bridgehub.L1Bridgehub.calldata_access_bytes_calldata_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common 

def A_calldata_access_bytes_calldata (value length : Identifier) (base_ref ptr : Literal) (s₀ s₉ : State) : Prop :=
  calldata_access_bytes_calldata_concrete_of_code.1 value length base_ref ptr s₀ s₉

lemma calldata_access_bytes_calldata_abs_of_concrete {s₀ s₉ : State} {value length base_ref ptr} :
  Spec (calldata_access_bytes_calldata_concrete_of_code.1 value length base_ref ptr) s₀ s₉ →
  Spec (A_calldata_access_bytes_calldata value length base_ref ptr) s₀ s₉ := by
  intro h
  simpa [A_calldata_access_bytes_calldata] using h

end

end generated.L1Bridgehub.L1Bridgehub
