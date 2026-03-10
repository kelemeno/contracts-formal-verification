import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_1810623666621152160
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_658041605499731378

import generated.L1AssetRouter.L1AssetRouter.Common.if_1254062856785940686_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_1254062856785940686 (s₀ s₉ : State) : Prop := True

lemma if_1254062856785940686_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1254062856785940686_concrete_of_code s₀ s₉ →
  Spec A_if_1254062856785940686 s₀ s₉ := by
  unfold A_if_1254062856785940686
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
