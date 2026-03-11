import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_9153090929313368865
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_799566292769261972

import generated.L1AssetRouter.L1AssetRouter.Common.if_1996614206653605388_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_1996614206653605388 (s₀ s₉ : State) : Prop :=
  if_1996614206653605388_concrete_of_code.1 s₀ s₉

lemma if_1996614206653605388_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1996614206653605388_concrete_of_code s₀ s₉ →
  Spec A_if_1996614206653605388 s₀ s₉ := by
  intro h
  simpa [A_if_1996614206653605388] using h

end

end L1AssetRouter.Common
