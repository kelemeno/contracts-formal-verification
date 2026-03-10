import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.if_666499110465816631_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_666499110465816631 (s₀ s₉ : State) : Prop := True

lemma if_666499110465816631_abs_of_concrete {s₀ s₉ : State} :
  Spec if_666499110465816631_concrete_of_code s₀ s₉ →
  Spec A_if_666499110465816631 s₀ s₉ := by
  unfold A_if_666499110465816631
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common
