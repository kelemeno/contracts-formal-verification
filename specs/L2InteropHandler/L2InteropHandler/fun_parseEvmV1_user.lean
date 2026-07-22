import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.fun_tryParseV1
import generated.L2InteropHandler.L2InteropHandler.Common.if_1138039834260901907
import generated.L2InteropHandler.L2InteropHandler.Common.if_4900129115500306496
import generated.L2InteropHandler.L2InteropHandler.Common.if_1741946688071961186
import generated.L2InteropHandler.L2InteropHandler.Common.switch_8231961504269039555
import generated.L2InteropHandler.L2InteropHandler.Common.if_6166908818084288343
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes

import generated.L2InteropHandler.L2InteropHandler.fun_parseEvmV1_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_fun_parseEvmV1 (var_chainId var_addr : Identifier) (var_self_3868_mpos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_parseEvmV1_abs_of_concrete {s₀ s₉ : State} {var_chainId var_addr var_self_3868_mpos} :
  Spec (fun_parseEvmV1_concrete_of_code.1 var_chainId var_addr var_self_3868_mpos) s₀ s₉ →
  Spec (A_fun_parseEvmV1 var_chainId var_addr var_self_3868_mpos) s₀ s₉ := by
  unfold fun_parseEvmV1_concrete_of_code A_fun_parseEvmV1
  sorry

end

end generated.L2InteropHandler.L2InteropHandler
