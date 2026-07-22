import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.array_allocation_size_array_bytes_dyn

import generated.L2AssetRouter.L2AssetRouter.Common.block_4787811467592878326_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_4787811467592878326 (s₀ s₉ : State) : Prop := sorry

lemma block_4787811467592878326_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4787811467592878326_concrete_of_code s₀ s₉ →
  Spec A_block_4787811467592878326 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
