import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2600721580863995212
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x32

import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_memory_array_index_access_struct_InteropCall_dyn (addr : Identifier) (baseRef index : Literal) (s₀ s₉ : State) : Prop := memory_array_index_access_struct_InteropCall_dyn_concrete_of_code.1 addr baseRef index s₀ s₉

lemma memory_array_index_access_struct_InteropCall_dyn_abs_of_concrete {s₀ s₉ : State} {addr baseRef index} :
  Spec (memory_array_index_access_struct_InteropCall_dyn_concrete_of_code.1 addr baseRef index) s₀ s₉ →
  Spec (A_memory_array_index_access_struct_InteropCall_dyn addr baseRef index) s₀ s₉ := by
  intro h
  simpa [A_memory_array_index_access_struct_InteropCall_dyn] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
