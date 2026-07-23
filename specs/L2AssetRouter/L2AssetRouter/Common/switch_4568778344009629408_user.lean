import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.fun_setAssetHandler
import generated.L2AssetRouter.L2AssetRouter.Common.if_7794561980809165501
import generated.L2AssetRouter.L2AssetRouter.Common.block_343298627753841545
import generated.L2AssetRouter.L2AssetRouter.Common.block_6459688961663567866
import generated.L2AssetRouter.L2AssetRouter.abi_encode_uint256_bytes32_bytes_calldata
import generated.L2AssetRouter.L2AssetRouter.Common.if_6864078037843212115
import generated.L2AssetRouter.L2AssetRouter.revert_forward
import generated.L2AssetRouter.L2AssetRouter.Common.if_401849216355358897
import generated.L2AssetRouter.L2AssetRouter.finalize_allocation
import generated.L2AssetRouter.L2AssetRouter.abi_decode
import generated.L2AssetRouter.L2AssetRouter.Common.if_4867595072135923888
import generated.L2AssetRouter.L2AssetRouter.Common.block_6910470754981286669
import generated.L2AssetRouter.L2AssetRouter.Common.block_7452105710916545113
import generated.L2AssetRouter.L2AssetRouter.Common.if_1475492890989233506
import generated.L2AssetRouter.L2AssetRouter.Common.if_5273053676196884472

import generated.L2AssetRouter.L2AssetRouter.Common.switch_4568778344009629408_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_switch_4568778344009629408 (s₀ s₉ : State) : Prop := switch_4568778344009629408_concrete_of_code.1 s₀ s₉

lemma switch_4568778344009629408_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_4568778344009629408_concrete_of_code s₀ s₉ →
  Spec A_switch_4568778344009629408 s₀ s₉ := by
  intro h
  simpa [A_switch_4568778344009629408] using h

end

end L2AssetRouter.Common
