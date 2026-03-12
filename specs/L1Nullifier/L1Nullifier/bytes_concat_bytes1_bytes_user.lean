import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation

import generated.L1Nullifier.L1Nullifier.bytes_concat_bytes1_bytes_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_bytes_concat_bytes1_bytes (outPtr : Identifier) (param param_1 : Literal) (s₀ s₉ : State) : Prop :=
  bytes_concat_bytes1_bytes_concrete_of_code.1 outPtr param param_1 s₀ s₉

lemma bytes_concat_bytes1_bytes_abs_of_concrete {s₀ s₉ : State} {outPtr param param_1} :
  Spec (bytes_concat_bytes1_bytes_concrete_of_code.1 outPtr param param_1) s₀ s₉ →
  Spec (A_bytes_concat_bytes1_bytes outPtr param param_1) s₀ s₉ := by
  intro h
  simpa [A_bytes_concat_bytes1_bytes] using h

end

end generated.L1Nullifier.L1Nullifier
