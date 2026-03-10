import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_4148053531410514966
import generated.L1Nullifier.L1Nullifier.panic_error_0x41

import generated.L1Nullifier.L1Nullifier.array_allocation_size_bytes_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_array_allocation_size_bytes (size : Identifier) (length : Literal) (s₀ s₉ : State) : Prop := True

lemma array_allocation_size_bytes_abs_of_concrete {s₀ s₉ : State} {size length} :
  Spec (array_allocation_size_bytes_concrete_of_code.1 size length) s₀ s₉ →
  Spec (A_array_allocation_size_bytes size length) s₀ s₉ := by
  unfold A_array_allocation_size_bytes
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
