import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.if_8832779172174931881_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_8832779172174931881 (s₀ s₉ : State) : Prop := True

lemma if_8832779172174931881_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8832779172174931881_concrete_of_code s₀ s₉ →
  Spec A_if_8832779172174931881 s₀ s₉ := by
  unfold A_if_8832779172174931881
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common
