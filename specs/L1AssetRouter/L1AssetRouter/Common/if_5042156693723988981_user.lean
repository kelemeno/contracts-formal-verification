import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_115229282105775987
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory

import generated.L1AssetRouter.L1AssetRouter.Common.if_5042156693723988981_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_5042156693723988981 (s₀ s₉ : State) : Prop := True

lemma if_5042156693723988981_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5042156693723988981_concrete_of_code s₀ s₉ →
  Spec A_if_5042156693723988981 s₀ s₉ := by
  unfold A_if_5042156693723988981
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
