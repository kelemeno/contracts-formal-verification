import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_5839106564881554340
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_3893721451317152461

import generated.L1AssetRouter.L1AssetRouter.Common.if_5565014839478708744_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_5565014839478708744 (s₀ s₉ : State) : Prop := True

lemma if_5565014839478708744_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5565014839478708744_concrete_of_code s₀ s₉ →
  Spec A_if_5565014839478708744 s₀ s₉ := by
  unfold A_if_5565014839478708744
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
