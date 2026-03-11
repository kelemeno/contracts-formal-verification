import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation_17765

import generated.L1Nullifier.L1Nullifier.allocate_and_zero_memory_struct_struct_L2Log_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_allocate_and_zero_memory_struct_struct_L2Log (memPtr : Identifier)  (s₀ s₉ : State) : Prop :=
  allocate_and_zero_memory_struct_struct_L2Log_concrete_of_code.1 memPtr s₀ s₉

lemma allocate_and_zero_memory_struct_struct_L2Log_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_and_zero_memory_struct_struct_L2Log_concrete_of_code.1 memPtr) s₀ s₉ →
  Spec (A_allocate_and_zero_memory_struct_struct_L2Log memPtr) s₀ s₉ := by
  intro h
  simpa [A_allocate_and_zero_memory_struct_struct_L2Log] using h

end

end generated.L1Nullifier.L1Nullifier
