import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.finalize_allocation
import generated.L2AssetRouter.L2AssetRouter.abi_decode

import generated.L2AssetRouter.L2AssetRouter.Common.if_401849216355358897_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_if_401849216355358897 (s₀ s₉ : State) : Prop := if_401849216355358897_concrete_of_code.1 s₀ s₉

lemma if_401849216355358897_abs_of_concrete {s₀ s₉ : State} :
  Spec if_401849216355358897_concrete_of_code s₀ s₉ →
  Spec A_if_401849216355358897 s₀ s₉ := by
  intro h
  simpa [A_if_401849216355358897] using h

end

end L2AssetRouter.Common
