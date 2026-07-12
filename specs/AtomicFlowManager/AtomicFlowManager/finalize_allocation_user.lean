import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_801497109727252421
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6033096439800527865
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5792510925045852942
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x41

import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_finalize_allocation  (memPtr size : Literal) (s₀ s₉ : State) : Prop := finalize_allocation_concrete_of_code.1  memPtr size s₀ s₉

lemma finalize_allocation_abs_of_concrete {s₀ s₉ : State} { memPtr size} :
  Spec (finalize_allocation_concrete_of_code.1  memPtr size) s₀ s₉ →
  Spec (A_finalize_allocation  memPtr size) s₀ s₉ := by
  intro h
  simpa [A_finalize_allocation] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
