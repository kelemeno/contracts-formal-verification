import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_array_array_bytes_dyn
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation_27947

import generated.L1AssetRouter.L1AssetRouter.Common.block_5464026732896519597_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_block_5464026732896519597 (s₀ s₉ : State) : Prop := block_5464026732896519597_concrete_of_code.1 s₀ s₉

lemma block_5464026732896519597_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5464026732896519597_concrete_of_code s₀ s₉ →
  Spec A_block_5464026732896519597 s₀ s₉ := by
  intro h
  simpa [A_block_5464026732896519597] using h

end

end L1AssetRouter.Common
