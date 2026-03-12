import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_5712827528392086091
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory

import generated.L1AssetRouter.L1AssetRouter.Common.if_3219152564164217733_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_3219152564164217733 (s₀ s₉ : State) : Prop :=
  if_3219152564164217733_concrete_of_code.1 s₀ s₉

lemma if_3219152564164217733_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3219152564164217733_concrete_of_code s₀ s₉ →
  Spec A_if_3219152564164217733 s₀ s₉ := by
  intro h
  simpa [A_if_3219152564164217733] using h

end

end L1AssetRouter.Common
