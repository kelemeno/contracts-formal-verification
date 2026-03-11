import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.panic_error_0x41

import generated.L1Nullifier.L1Nullifier.finalize_allocation_17765_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_finalize_allocation_17765  (memPtr : Literal) (s₀ s₉ : State) : Prop := True

lemma finalize_allocation_17765_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (finalize_allocation_17765_concrete_of_code.1 memPtr) s₀ s₉ →
  Spec (A_finalize_allocation_17765 memPtr) s₀ s₉ := by
  unfold A_finalize_allocation_17765
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
