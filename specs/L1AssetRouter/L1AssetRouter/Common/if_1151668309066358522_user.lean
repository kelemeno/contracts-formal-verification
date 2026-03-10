import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_6211775506654671746
import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes
import generated.L1AssetRouter.L1AssetRouter.Common.if_1545208373430012938
import generated.L1AssetRouter.L1AssetRouter.Common.if_1974957643560532488
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.if_1151668309066358522_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_1151668309066358522 (s₀ s₉ : State) : Prop := True

lemma if_1151668309066358522_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1151668309066358522_concrete_of_code s₀ s₉ →
  Spec A_if_1151668309066358522 s₀ s₉ := by
  unfold A_if_1151668309066358522
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
