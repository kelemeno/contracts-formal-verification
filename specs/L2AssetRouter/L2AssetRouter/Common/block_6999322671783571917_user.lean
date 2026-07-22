import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.calldata_array_index_range_access_bytes_calldata_11759
import generated.L2AssetRouter.L2AssetRouter.abi_decode_uint256t_bytes32t_bytes
import generated.L2AssetRouter.L2AssetRouter.constant_L2_NATIVE_TOKEN_VAULT_ADDR
import generated.L2AssetRouter.L2AssetRouter.cleanup_address

import generated.L2AssetRouter.L2AssetRouter.Common.block_6999322671783571917_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_6999322671783571917 (s₀ s₉ : State) : Prop := sorry

lemma block_6999322671783571917_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6999322671783571917_concrete_of_code s₀ s₉ →
  Spec A_block_6999322671783571917 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
