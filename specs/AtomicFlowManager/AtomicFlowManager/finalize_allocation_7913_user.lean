import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1966118315202180062
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x41

import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation_7913_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_finalize_allocation_7913  (memPtr : Literal) (s₀ s₉ : State) : Prop := sorry

lemma finalize_allocation_7913_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (finalize_allocation_7913_concrete_of_code.1  memPtr) s₀ s₉ →
  Spec (A_finalize_allocation_7913  memPtr) s₀ s₉ := by
  unfold finalize_allocation_7913_concrete_of_code A_finalize_allocation_7913
  sorry

end

end generated.AtomicFlowManager.AtomicFlowManager
