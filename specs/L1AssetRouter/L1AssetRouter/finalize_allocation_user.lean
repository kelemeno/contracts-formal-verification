import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_3489657594510812776

import generated.L1AssetRouter.L1AssetRouter.finalize_allocation_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common

def A_finalize_allocation (memPtr size : Literal) (s₀ s₉ : State) : Prop :=
  finalize_allocation_concrete_of_code.1 memPtr size s₀ s₉

lemma finalize_allocation_abs_of_concrete {s₀ s₉ : State} {memPtr size} :
  Spec (finalize_allocation_concrete_of_code.1 memPtr size) s₀ s₉ →
  Spec (A_finalize_allocation memPtr size) s₀ s₉ := by
  intro h
  simpa [A_finalize_allocation] using h

end

end generated.L1AssetRouter.L1AssetRouter
