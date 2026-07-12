import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_4148053531410514966
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x41

import generated.AtomicFlowManager.AtomicFlowManager.array_allocation_size_array_struct_InteropCall_dyn_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_array_allocation_size_array_struct_InteropCall_dyn (size : Identifier) (length : Literal) (s₀ s₉ : State) : Prop := array_allocation_size_array_struct_InteropCall_dyn_concrete_of_code.1 size length s₀ s₉

lemma array_allocation_size_array_struct_InteropCall_dyn_abs_of_concrete {s₀ s₉ : State} {size length} :
  Spec (array_allocation_size_array_struct_InteropCall_dyn_concrete_of_code.1 size length) s₀ s₉ →
  Spec (A_array_allocation_size_array_struct_InteropCall_dyn size length) s₀ s₉ := by
  intro h
  simpa [A_array_allocation_size_array_struct_InteropCall_dyn] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
