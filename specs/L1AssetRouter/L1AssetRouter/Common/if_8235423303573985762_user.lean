import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_5712827528392086091
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory

import generated.L1AssetRouter.L1AssetRouter.Common.if_8235423303573985762_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_8235423303573985762 (s₀ s₉ : State) : Prop := sorry

lemma if_8235423303573985762_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8235423303573985762_concrete_of_code s₀ s₉ →
  Spec A_if_8235423303573985762 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
