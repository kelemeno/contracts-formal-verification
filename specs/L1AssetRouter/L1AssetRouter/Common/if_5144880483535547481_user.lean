import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_5144880483535547481_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_5144880483535547481 (s₀ s₉ : State) : Prop := True

lemma if_5144880483535547481_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5144880483535547481_concrete_of_code s₀ s₉ →
  Spec A_if_5144880483535547481 s₀ s₉ := by
  unfold A_if_5144880483535547481
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
