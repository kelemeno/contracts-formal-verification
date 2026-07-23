import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.update_storage_value_offset_uint256_to_uint256
import generated.L2AssetRouter.L2AssetRouter.read_from_storage_split_offset_address_11714

import generated.L2AssetRouter.L2AssetRouter.Common.block_6012763339103030502_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_6012763339103030502 (s₀ s₉ : State) : Prop := block_6012763339103030502_concrete_of_code.1 s₀ s₉

lemma block_6012763339103030502_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6012763339103030502_concrete_of_code s₀ s₉ →
  Spec A_block_6012763339103030502 s₀ s₉ := by
  intro h
  simpa [A_block_6012763339103030502] using h

end

end L2AssetRouter.Common
