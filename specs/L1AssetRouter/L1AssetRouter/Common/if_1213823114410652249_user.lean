import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_2861284523879141151
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_264198839584058225

import generated.L1AssetRouter.L1AssetRouter.Common.if_1213823114410652249_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_1213823114410652249 (s₀ s₉ : State) : Prop := True

lemma if_1213823114410652249_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1213823114410652249_concrete_of_code s₀ s₉ →
  Spec A_if_1213823114410652249 s₀ s₉ := by
  unfold A_if_1213823114410652249
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
