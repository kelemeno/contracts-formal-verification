import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.constant_L2_NATIVE_TOKEN_VAULT_ADDR
import generated.L2AssetRouter.L2AssetRouter.mapping_index_access_mapping_bytes32_address_of_bytes32
import generated.L2AssetRouter.L2AssetRouter.read_from_storage_split_offset_address

import generated.L2AssetRouter.L2AssetRouter.Common.block_3694856571280274132_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_3694856571280274132 (s₀ s₉ : State) : Prop := block_3694856571280274132_concrete_of_code.1 s₀ s₉

lemma block_3694856571280274132_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3694856571280274132_concrete_of_code s₀ s₉ →
  Spec A_block_3694856571280274132 s₀ s₉ := by
  intro h
  simpa [A_block_3694856571280274132] using h

end

end L2AssetRouter.Common
