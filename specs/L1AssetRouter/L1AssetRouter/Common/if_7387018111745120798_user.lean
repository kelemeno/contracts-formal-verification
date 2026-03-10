import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_7387018111745120798_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_7387018111745120798 (s₀ s₉ : State) : Prop := True

lemma if_7387018111745120798_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7387018111745120798_concrete_of_code s₀ s₉ →
  Spec A_if_7387018111745120798 s₀ s₉ := by
  unfold A_if_7387018111745120798
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
