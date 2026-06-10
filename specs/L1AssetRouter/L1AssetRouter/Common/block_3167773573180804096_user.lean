import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner
import generated.L1AssetRouter.L1AssetRouter.fun_getDepositCalldata

import generated.L1AssetRouter.L1AssetRouter.Common.block_3167773573180804096_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_block_3167773573180804096 (s₀ s₉ : State) : Prop := block_3167773573180804096_concrete_of_code.1 s₀ s₉

lemma block_3167773573180804096_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3167773573180804096_concrete_of_code s₀ s₉ →
  Spec A_block_3167773573180804096 s₀ s₉ := by
  intro h
  simpa [A_block_3167773573180804096] using h

end

end L1AssetRouter.Common
