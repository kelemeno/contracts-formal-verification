import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation

import generated.AtomicFlowManager.AtomicFlowManager.allocate_memory_7429_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_allocate_memory_7429 (memPtr : Identifier)  (s₀ s₉ : State) : Prop := allocate_memory_7429_concrete_of_code.1 memPtr s₀ s₉

lemma allocate_memory_7429_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_memory_7429_concrete_of_code.1 memPtr ) s₀ s₉ →
  Spec (A_allocate_memory_7429 memPtr ) s₀ s₉ := by
  intro h
  simpa [A_allocate_memory_7429] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
