import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_6040632739308624336_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_6040632739308624336 (s₀ s₉ : State) : Prop := True

lemma if_6040632739308624336_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6040632739308624336_concrete_of_code s₀ s₉ →
  Spec A_if_6040632739308624336 s₀ s₉ := by
  unfold A_if_6040632739308624336
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
