import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address
import generated.L1AssetRouter.L1AssetRouter.Common.if_5680788495791948010
import generated.L1AssetRouter.L1AssetRouter.Common.if_1829154961882075037
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.if_4905610264939643226_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_4905610264939643226 (s₀ s₉ : State) : Prop := True

lemma if_4905610264939643226_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4905610264939643226_concrete_of_code s₀ s₉ →
  Spec A_if_4905610264939643226 s₀ s₉ := by
  unfold A_if_4905610264939643226
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
