import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.finalize_allocation
import generated.L2AssetRouter.L2AssetRouter.abi_decode_bytes_fromMemory

import generated.L2AssetRouter.L2AssetRouter.Common.if_2714870613723580744_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_if_2714870613723580744 (s₀ s₉ : State) : Prop := sorry

lemma if_2714870613723580744_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2714870613723580744_concrete_of_code s₀ s₉ →
  Spec A_if_2714870613723580744 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
