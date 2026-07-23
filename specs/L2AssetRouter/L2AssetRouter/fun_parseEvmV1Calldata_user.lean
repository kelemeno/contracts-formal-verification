import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.fun_tryParseV1Calldata
import generated.L2AssetRouter.L2AssetRouter.Common.if_1138039834260901907
import generated.L2AssetRouter.L2AssetRouter.Common.if_4078929471151748846
import generated.L2AssetRouter.L2AssetRouter.Common.if_7506617587990959785
import generated.L2AssetRouter.L2AssetRouter.Common.switch_6457325179704891626
import generated.L2AssetRouter.L2AssetRouter.convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes32
import generated.L2AssetRouter.L2AssetRouter.panic_error_0x11
import generated.L2AssetRouter.L2AssetRouter.convert_bytes20_to_address
import generated.L2AssetRouter.L2AssetRouter.require_helper_error_InteroperableAddressParsingError_bytes_calldata

import generated.L2AssetRouter.L2AssetRouter.fun_parseEvmV1Calldata_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_fun_parseEvmV1Calldata (var_chainId var_addr : Identifier) (var_self_offset var_self_4227_length : Literal) (s₀ s₉ : State) : Prop := fun_parseEvmV1Calldata_concrete_of_code.1 var_chainId var_addr var_self_offset var_self_4227_length s₀ s₉

lemma fun_parseEvmV1Calldata_abs_of_concrete {s₀ s₉ : State} {var_chainId var_addr var_self_offset var_self_4227_length} :
  Spec (fun_parseEvmV1Calldata_concrete_of_code.1 var_chainId var_addr var_self_offset var_self_4227_length) s₀ s₉ →
  Spec (A_fun_parseEvmV1Calldata var_chainId var_addr var_self_offset var_self_4227_length) s₀ s₉ := by
  intro h
  simpa [A_fun_parseEvmV1Calldata] using h

end

end generated.L2AssetRouter.L2AssetRouter
