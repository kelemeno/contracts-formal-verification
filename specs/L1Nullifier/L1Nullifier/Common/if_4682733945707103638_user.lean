import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.if_4682733945707103638_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_4682733945707103638 (s₀ s₉ : State) : Prop := True

lemma if_4682733945707103638_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4682733945707103638_concrete_of_code s₀ s₉ →
  Spec A_if_4682733945707103638 s₀ s₉ := by
  unfold A_if_4682733945707103638
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common
