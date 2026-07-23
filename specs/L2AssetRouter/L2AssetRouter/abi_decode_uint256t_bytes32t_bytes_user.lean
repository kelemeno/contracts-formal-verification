import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_7992633778145326824
import generated.L2AssetRouter.L2AssetRouter.Common.block_3972592979224134264
import generated.L2AssetRouter.L2AssetRouter.Common.block_5602705261336187008
import generated.L2AssetRouter.L2AssetRouter.Common.if_3680740834951988335
import generated.L2AssetRouter.L2AssetRouter.abi_decode_bytes

import generated.L2AssetRouter.L2AssetRouter.abi_decode_uint256t_bytes32t_bytes_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_abi_decode_uint256t_bytes32t_bytes (value0 value1 value2 : Identifier) (headStart dataEnd : Literal) (s₀ s₉ : State) : Prop := abi_decode_uint256t_bytes32t_bytes_concrete_of_code.1 value0 value1 value2 headStart dataEnd s₀ s₉

lemma abi_decode_uint256t_bytes32t_bytes_abs_of_concrete {s₀ s₉ : State} {value0 value1 value2 headStart dataEnd} :
  Spec (abi_decode_uint256t_bytes32t_bytes_concrete_of_code.1 value0 value1 value2 headStart dataEnd) s₀ s₉ →
  Spec (A_abi_decode_uint256t_bytes32t_bytes value0 value1 value2 headStart dataEnd) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_uint256t_bytes32t_bytes] using h

end

end generated.L2AssetRouter.L2AssetRouter
