import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation

import generated.L1Nullifier.L1Nullifier.allocate_memory_17639_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_allocate_memory_17639 (memPtr : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma allocate_memory_17639_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_memory_17639_concrete_of_code.1 memPtr ) s₀ s₉ →
  Spec (A_allocate_memory_17639 memPtr ) s₀ s₉ := by
  unfold allocate_memory_17639_concrete_of_code A_allocate_memory_17639
  sorry

end

end generated.L1Nullifier.L1Nullifier
