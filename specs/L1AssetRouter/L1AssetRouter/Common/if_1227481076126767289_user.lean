import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_7668669370823473420
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_311583620406563518

import generated.L1AssetRouter.L1AssetRouter.Common.if_1227481076126767289_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_1227481076126767289 (s₀ s₉ : State) : Prop := True

lemma if_1227481076126767289_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1227481076126767289_concrete_of_code s₀ s₉ →
  Spec A_if_1227481076126767289 s₀ s₉ := by
  unfold A_if_1227481076126767289
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
