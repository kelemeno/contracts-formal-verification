import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.abi_decode_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_abi_decode  (headStart dataEnd : Literal) (s₀ s₉ : State) : Prop :=
  abi_decode_concrete_of_code.1 headStart dataEnd s₀ s₉

lemma abi_decode_abs_of_concrete {s₀ s₉ : State} { headStart dataEnd} :
  Spec (abi_decode_concrete_of_code.1 headStart dataEnd) s₀ s₉ →
  Spec (A_abi_decode headStart dataEnd) s₀ s₉ := by
  intro h
  simpa [A_abi_decode] using h

end

end generated.L1Nullifier.L1Nullifier
