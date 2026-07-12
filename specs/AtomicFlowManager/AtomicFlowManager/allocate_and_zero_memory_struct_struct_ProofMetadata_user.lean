import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_912035191040110064
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation_7426
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4306212279716492877

import generated.AtomicFlowManager.AtomicFlowManager.allocate_and_zero_memory_struct_struct_ProofMetadata_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_allocate_and_zero_memory_struct_struct_ProofMetadata (memPtr : Identifier)  (s₀ s₉ : State) : Prop := allocate_and_zero_memory_struct_struct_ProofMetadata_concrete_of_code.1 memPtr s₀ s₉

lemma allocate_and_zero_memory_struct_struct_ProofMetadata_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_and_zero_memory_struct_struct_ProofMetadata_concrete_of_code.1 memPtr ) s₀ s₉ →
  Spec (A_allocate_and_zero_memory_struct_struct_ProofMetadata memPtr ) s₀ s₉ := by
  intro h
  simpa [A_allocate_and_zero_memory_struct_struct_ProofMetadata] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
