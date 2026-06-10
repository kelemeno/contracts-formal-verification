import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.block_9117733535954415247
import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.block_4220220579886616951

import generated.L1AssetRouter.L1AssetRouter.Common.switch_7341777802889238516_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_7341777802889238516 (s₀ s₉ : State) : Prop := switch_7341777802889238516_concrete_of_code.1 s₀ s₉

lemma switch_7341777802889238516_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_7341777802889238516_concrete_of_code s₀ s₉ →
  Spec A_switch_7341777802889238516 s₀ s₉ := by
  intro h
  simpa [A_switch_7341777802889238516] using h

end

end L1AssetRouter.Common
