import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_1366110598910321239

import generated.L1AssetRouter.L1AssetRouter.finalize_allocation_27947_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_finalize_allocation_27947  (memPtr : Literal) (s₀ s₉ : State) : Prop :=
  finalize_allocation_27947_concrete_of_code.1 memPtr s₀ s₉

lemma finalize_allocation_27947_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (finalize_allocation_27947_concrete_of_code.1  memPtr) s₀ s₉ →
  Spec (A_finalize_allocation_27947  memPtr) s₀ s₉ := by
  intro h
  simpa [A_finalize_allocation_27947] using h

end

end generated.L1AssetRouter.L1AssetRouter
