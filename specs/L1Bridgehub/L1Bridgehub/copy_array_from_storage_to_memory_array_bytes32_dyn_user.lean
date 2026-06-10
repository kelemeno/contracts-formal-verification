import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.for_2051255765951039157
import generated.L1Bridgehub.L1Bridgehub.finalize_allocation

import generated.L1Bridgehub.L1Bridgehub.copy_array_from_storage_to_memory_array_bytes32_dyn_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common generated.L1Bridgehub L1Bridgehub

def A_copy_array_from_storage_to_memory_array_bytes32_dyn (memPtr : Identifier)  (s₀ s₉ : State) : Prop := copy_array_from_storage_to_memory_array_bytes32_dyn_concrete_of_code.1 memPtr s₀ s₉

lemma copy_array_from_storage_to_memory_array_bytes32_dyn_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (copy_array_from_storage_to_memory_array_bytes32_dyn_concrete_of_code.1 memPtr ) s₀ s₉ →
  Spec (A_copy_array_from_storage_to_memory_array_bytes32_dyn memPtr ) s₀ s₉ := by
  intro h
  simpa [A_copy_array_from_storage_to_memory_array_bytes32_dyn] using h

end

end generated.L1Bridgehub.L1Bridgehub
