import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.fun_tryParseV1
import generated.InteropHandler.InteropHandler.Common.if_1138039834260901907
import generated.InteropHandler.InteropHandler.Common.if_4900129115500306496
import generated.InteropHandler.InteropHandler.Common.if_1741946688071961186
import generated.InteropHandler.InteropHandler.Common.switch_8231961504269039555
import generated.InteropHandler.InteropHandler.Common.if_1372087451824215729
import generated.InteropHandler.InteropHandler.abi_encode_bytes

import generated.InteropHandler.InteropHandler.fun_parseEvmV1_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_fun_parseEvmV1 (var_chainId var_addr : Identifier) (var_self_mpos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_parseEvmV1_abs_of_concrete {s₀ s₉ : State} {var_chainId var_addr var_self_mpos} :
  Spec (fun_parseEvmV1_concrete_of_code.1 var_chainId var_addr var_self_mpos) s₀ s₉ →
  Spec (A_fun_parseEvmV1 var_chainId var_addr var_self_mpos) s₀ s₉ := by
  unfold fun_parseEvmV1_concrete_of_code A_fun_parseEvmV1
  sorry

end

end generated.InteropHandler.InteropHandler
