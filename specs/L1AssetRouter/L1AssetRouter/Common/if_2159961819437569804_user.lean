import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_5144880483535547481
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory

import generated.L1AssetRouter.L1AssetRouter.Common.if_2159961819437569804_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_2159961819437569804 (s₀ s₉ : State) : Prop :=
  if_2159961819437569804_concrete_of_code.1 s₀ s₉

lemma if_2159961819437569804_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2159961819437569804_concrete_of_code s₀ s₉ →
  Spec A_if_2159961819437569804 s₀ s₉ := by
  intro h
  simpa [A_if_2159961819437569804] using h

end

end L1AssetRouter.Common
