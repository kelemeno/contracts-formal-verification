import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address
import generated.L1AssetRouter.L1AssetRouter.Common.if_4521731106176019512
import generated.L1AssetRouter.L1AssetRouter.Common.if_5718206110945243169
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_4905610264939643226
import generated.L1AssetRouter.L1AssetRouter.Common.if_6347281329581904638

import generated.L1AssetRouter.L1AssetRouter.Common.switch_7614661687758543566_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_7614661687758543566 (s₀ s₉ : State) : Prop := True

lemma switch_7614661687758543566_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_7614661687758543566_concrete_of_code s₀ s₉ →
  Spec A_switch_7614661687758543566 s₀ s₉ := by
  unfold A_switch_7614661687758543566
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
