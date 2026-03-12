import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.abi_encode_bytes_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_abi_encode_bytes (end_clear_sanitised_hrafn : Identifier) (value pos : Literal) (s₀ s₉ : State) : Prop :=
  abi_encode_bytes_concrete_of_code.1 end_clear_sanitised_hrafn value pos s₀ s₉

lemma abi_encode_bytes_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn value pos} :
  Spec (abi_encode_bytes_concrete_of_code.1 end_clear_sanitised_hrafn value pos) s₀ s₉ →
  Spec (A_abi_encode_bytes end_clear_sanitised_hrafn value pos) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_bytes] using h

end

end generated.L1Nullifier.L1Nullifier
