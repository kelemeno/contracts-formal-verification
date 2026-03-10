import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.switch_8026941473334182912
import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes
import generated.L1AssetRouter.L1AssetRouter.Common.if_5198757265867716647

import generated.L1AssetRouter.L1AssetRouter.Common.switch_5364585472786756111_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_5364585472786756111 (s₀ s₉ : State) : Prop := True

lemma switch_5364585472786756111_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_5364585472786756111_concrete_of_code s₀ s₉ →
  Spec A_switch_5364585472786756111 s₀ s₉ := by
  unfold A_switch_5364585472786756111
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
