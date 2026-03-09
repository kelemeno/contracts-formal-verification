import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_6530158971123141721
import generated.L1Nullifier.L1Nullifier.panic_error_0x41

import generated.L1Nullifier.L1Nullifier.allocate_and_zero_memory_struct_struct_L2Message_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_allocate_and_zero_memory_struct_struct_L2Message (memPtr : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma allocate_and_zero_memory_struct_struct_L2Message_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_and_zero_memory_struct_struct_L2Message_concrete_of_code.1 memPtr ) s₀ s₉ →
  Spec (A_allocate_and_zero_memory_struct_struct_L2Message memPtr ) s₀ s₉ := by
  unfold allocate_and_zero_memory_struct_struct_L2Message_concrete_of_code A_allocate_and_zero_memory_struct_struct_L2Message
  sorry

end

end generated.L1Nullifier.L1Nullifier
