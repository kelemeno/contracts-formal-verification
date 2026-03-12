import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.panic_error_0x41

import generated.L1Nullifier.L1Nullifier.finalize_allocation_17735_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_finalize_allocation_17735  (memPtr : Literal) (s₀ s₉ : State) : Prop :=
  finalize_allocation_17735_concrete_of_code.1 memPtr s₀ s₉

lemma finalize_allocation_17735_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (finalize_allocation_17735_concrete_of_code.1 memPtr) s₀ s₉ →
  Spec (A_finalize_allocation_17735 memPtr) s₀ s₉ := by
  intro h
  simpa [A_finalize_allocation_17735] using h

end

end generated.L1Nullifier.L1Nullifier
