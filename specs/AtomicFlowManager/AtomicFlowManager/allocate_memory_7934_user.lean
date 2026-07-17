import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation

import generated.AtomicFlowManager.AtomicFlowManager.allocate_memory_7934_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_allocate_memory_7934 (memPtr : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma allocate_memory_7934_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_memory_7934_concrete_of_code.1 memPtr ) s₀ s₉ →
  Spec (A_allocate_memory_7934 memPtr ) s₀ s₉ := by
  unfold allocate_memory_7934_concrete_of_code A_allocate_memory_7934
  sorry

end

end generated.AtomicFlowManager.AtomicFlowManager
