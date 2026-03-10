import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.mcopy

import generated.L1AssetRouter.L1AssetRouter.Common.switch_8145808823390256759_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_switch_8145808823390256759 (s₀ s₉ : State) : Prop := True

lemma switch_8145808823390256759_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8145808823390256759_concrete_of_code s₀ s₉ →
  Spec A_switch_8145808823390256759 s₀ s₉ := by
  unfold A_switch_8145808823390256759
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
