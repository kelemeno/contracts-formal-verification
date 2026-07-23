import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner
import generated.L2AssetRouter.L2AssetRouter.fun_getDepositCalldata

import generated.L2AssetRouter.L2AssetRouter.Common.block_2415779567920543028_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_2415779567920543028 (s₀ s₉ : State) : Prop := block_2415779567920543028_concrete_of_code.1 s₀ s₉

lemma block_2415779567920543028_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2415779567920543028_concrete_of_code s₀ s₉ →
  Spec A_block_2415779567920543028 s₀ s₉ := by
  intro h
  simpa [A_block_2415779567920543028] using h

end

end L2AssetRouter.Common
