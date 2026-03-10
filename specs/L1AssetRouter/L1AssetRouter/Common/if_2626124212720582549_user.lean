import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_2626124212720582549_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_2626124212720582549 (s₀ s₉ : State) : Prop := True

lemma if_2626124212720582549_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2626124212720582549_concrete_of_code s₀ s₉ →
  Spec A_if_2626124212720582549 s₀ s₉ := by
  unfold A_if_2626124212720582549
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
