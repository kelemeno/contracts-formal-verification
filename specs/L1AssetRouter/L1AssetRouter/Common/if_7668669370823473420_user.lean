import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_7668669370823473420_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_7668669370823473420 (s₀ s₉ : State) : Prop := True

lemma if_7668669370823473420_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7668669370823473420_concrete_of_code s₀ s₉ →
  Spec A_if_7668669370823473420 s₀ s₉ := by
  unfold A_if_7668669370823473420
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
