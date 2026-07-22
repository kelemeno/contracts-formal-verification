import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.validator_revert_contract_IL1AssetRouter

import generated.L2AssetRouter.L2AssetRouter.Common.block_591892474146335214_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_591892474146335214 (s₀ s₉ : State) : Prop := sorry

lemma block_591892474146335214_abs_of_concrete {s₀ s₉ : State} :
  Spec block_591892474146335214_concrete_of_code s₀ s₉ →
  Spec A_block_591892474146335214 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
