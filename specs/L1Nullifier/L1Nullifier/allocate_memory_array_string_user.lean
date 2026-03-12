import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_6861713686796867628
import generated.L1Nullifier.L1Nullifier.panic_error_0x41
import generated.L1Nullifier.L1Nullifier.finalize_allocation

import generated.L1Nullifier.L1Nullifier.allocate_memory_array_string_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_allocate_memory_array_string (memPtr : Identifier)  (s₀ s₉ : State) : Prop :=
  allocate_memory_array_string_concrete_of_code.1 memPtr s₀ s₉

lemma allocate_memory_array_string_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_memory_array_string_concrete_of_code.1 memPtr) s₀ s₉ →
  Spec (A_allocate_memory_array_string memPtr) s₀ s₉ := by
  intro h
  simpa [A_allocate_memory_array_string] using h

end

end generated.L1Nullifier.L1Nullifier
