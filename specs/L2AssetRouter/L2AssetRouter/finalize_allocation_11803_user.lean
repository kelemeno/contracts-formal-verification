import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_1966118315202180062
import generated.L2AssetRouter.L2AssetRouter.panic_error_0x41

import generated.L2AssetRouter.L2AssetRouter.finalize_allocation_11803_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_finalize_allocation_11803  (memPtr : Literal) (s₀ s₉ : State) : Prop := finalize_allocation_11803_concrete_of_code.1 memPtr s₀ s₉

lemma finalize_allocation_11803_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (finalize_allocation_11803_concrete_of_code.1  memPtr) s₀ s₉ →
  Spec (A_finalize_allocation_11803  memPtr) s₀ s₉ := by
  intro h
  simpa [A_finalize_allocation_11803] using h

end

end generated.L2AssetRouter.L2AssetRouter
