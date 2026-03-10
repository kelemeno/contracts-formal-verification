import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_4309819468703589176
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_4425277895281822204

import generated.L1AssetRouter.L1AssetRouter.Common.if_8154557830264771290_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_8154557830264771290 (s₀ s₉ : State) : Prop := True

lemma if_8154557830264771290_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8154557830264771290_concrete_of_code s₀ s₉ →
  Spec A_if_8154557830264771290 s₀ s₉ := by
  unfold A_if_8154557830264771290
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
