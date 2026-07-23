import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_1366110598910321239

import generated.L2InteropHandler.L2InteropHandler.finalize_allocation_22021_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_finalize_allocation_22021  (memPtr : Literal) (s₀ s₉ : State) : Prop := finalize_allocation_22021_concrete_of_code.1 memPtr s₀ s₉

lemma finalize_allocation_22021_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (finalize_allocation_22021_concrete_of_code.1  memPtr) s₀ s₉ →
  Spec (A_finalize_allocation_22021  memPtr) s₀ s₉ := by
  intro h
  simpa [A_finalize_allocation_22021] using h

end

end generated.L2InteropHandler.L2InteropHandler
