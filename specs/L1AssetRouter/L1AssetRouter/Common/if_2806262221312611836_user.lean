import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_2806262221312611836_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_2806262221312611836 (s₀ s₉ : State) : Prop := True

lemma if_2806262221312611836_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2806262221312611836_concrete_of_code s₀ s₉ →
  Spec A_if_2806262221312611836 s₀ s₉ := by
  unfold A_if_2806262221312611836
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
