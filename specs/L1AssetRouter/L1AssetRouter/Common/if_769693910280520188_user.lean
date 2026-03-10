import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_1384984673001299506
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_3867399954127536454

import generated.L1AssetRouter.L1AssetRouter.Common.if_769693910280520188_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_769693910280520188 (s₀ s₉ : State) : Prop := True

lemma if_769693910280520188_abs_of_concrete {s₀ s₉ : State} :
  Spec if_769693910280520188_concrete_of_code s₀ s₉ →
  Spec A_if_769693910280520188 s₀ s₉ := by
  unfold A_if_769693910280520188
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
