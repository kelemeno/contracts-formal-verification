import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_7504501281547084377
import generated.L1AssetRouter.L1AssetRouter.Common.if_5561360400113959191
import generated.L1AssetRouter.L1AssetRouter.Common.if_3184704065110235532
import generated.L1AssetRouter.L1AssetRouter.Common.if_1038707842519896549
import generated.L1AssetRouter.L1AssetRouter.Common.if_3680740834951988335
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes

import generated.L1AssetRouter.L1AssetRouter.Common.switch_5528132988775090082_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_5528132988775090082 (s₀ s₉ : State) : Prop :=
  switch_5528132988775090082_concrete_of_code.1 s₀ s₉

lemma switch_5528132988775090082_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_5528132988775090082_concrete_of_code s₀ s₉ →
  Spec A_switch_5528132988775090082 s₀ s₉ := by
  intro h
  simpa [A_switch_5528132988775090082] using h

end

end L1AssetRouter.Common
