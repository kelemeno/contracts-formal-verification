import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_1366110598910321239

import generated.InteropHandler.InteropHandler.finalize_allocation_21285_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

def A_finalize_allocation_21285  (memPtr : Literal) (s₀ s₉ : State) : Prop := sorry

lemma finalize_allocation_21285_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (finalize_allocation_21285_concrete_of_code.1  memPtr) s₀ s₉ →
  Spec (A_finalize_allocation_21285  memPtr) s₀ s₉ := by
  unfold finalize_allocation_21285_concrete_of_code A_finalize_allocation_21285
  sorry

end

end generated.InteropHandler.InteropHandler
