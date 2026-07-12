import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.array_allocation_size_array_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3502045432915694067_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_3502045432915694067 (s₀ s₉ : State) : Prop := block_3502045432915694067_concrete_of_code.1 s₀ s₉

lemma block_3502045432915694067_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3502045432915694067_concrete_of_code s₀ s₉ →
  Spec A_block_3502045432915694067 s₀ s₉ := by
  intro h
  simpa [A_block_3502045432915694067] using h

end

end AtomicFlowManager.Common
