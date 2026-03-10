import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_1384984673001299506_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_1384984673001299506 (s₀ s₉ : State) : Prop := True

lemma if_1384984673001299506_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1384984673001299506_concrete_of_code s₀ s₉ →
  Spec A_if_1384984673001299506 s₀ s₉ := by
  unfold A_if_1384984673001299506
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
