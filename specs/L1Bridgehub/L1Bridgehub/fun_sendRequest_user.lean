import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.switch_8805183917919185541
import generated.L1Bridgehub.L1Bridgehub.fun_get
import generated.L1Bridgehub.L1Bridgehub.abi_encode_bytes
import generated.L1Bridgehub.L1Bridgehub.Common.for_1639041582502888472
import generated.L1Bridgehub.L1Bridgehub.Common.if_3726317777273006065
import generated.L1Bridgehub.L1Bridgehub.Common.if_1574415747812902126
import generated.L1Bridgehub.L1Bridgehub.finalize_allocation

import generated.L1Bridgehub.L1Bridgehub.fun_sendRequest_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common generated.L1Bridgehub L1Bridgehub

def A_fun_sendRequest (var_canonicalTxHash : Identifier) (var_chainId var_refundRecipient var_request_mpos : Literal) (s₀ s₉ : State) : Prop :=
  fun_sendRequest_concrete_of_code.1 var_canonicalTxHash var_chainId var_refundRecipient var_request_mpos s₀ s₉

lemma fun_sendRequest_abs_of_concrete {s₀ s₉ : State} {var_canonicalTxHash var_chainId var_refundRecipient var_request_mpos} :
  Spec (fun_sendRequest_concrete_of_code.1 var_canonicalTxHash var_chainId var_refundRecipient var_request_mpos) s₀ s₉ →
  Spec (A_fun_sendRequest var_canonicalTxHash var_chainId var_refundRecipient var_request_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_sendRequest] using h

end

end generated.L1Bridgehub.L1Bridgehub
