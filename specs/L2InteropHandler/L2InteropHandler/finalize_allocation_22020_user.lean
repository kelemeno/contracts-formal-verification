import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_1366110598910321239

import generated.L2InteropHandler.L2InteropHandler.finalize_allocation_22020_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_finalize_allocation_22020  (memPtr : Literal) (s₀ s₉ : State) : Prop := sorry

lemma finalize_allocation_22020_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (finalize_allocation_22020_concrete_of_code.1  memPtr) s₀ s₉ →
  Spec (A_finalize_allocation_22020  memPtr) s₀ s₉ := by
  unfold finalize_allocation_22020_concrete_of_code A_finalize_allocation_22020
  sorry

end

end generated.L2InteropHandler.L2InteropHandler
