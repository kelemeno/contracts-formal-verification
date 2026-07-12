import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1966118315202180062
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x41
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2281065446741902325
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_766924542922581316
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5690683828684622158
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3856516188989530295

import generated.AtomicFlowManager.AtomicFlowManager.allocate_and_zero_memory_struct_struct_ProofData_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_allocate_and_zero_memory_struct_struct_ProofData (memPtr : Identifier)  (s₀ s₉ : State) : Prop := allocate_and_zero_memory_struct_struct_ProofData_concrete_of_code.1 memPtr s₀ s₉

lemma allocate_and_zero_memory_struct_struct_ProofData_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_and_zero_memory_struct_struct_ProofData_concrete_of_code.1 memPtr ) s₀ s₉ →
  Spec (A_allocate_and_zero_memory_struct_struct_ProofData memPtr ) s₀ s₉ := by
  intro h
  simpa [A_allocate_and_zero_memory_struct_struct_ProofData] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
