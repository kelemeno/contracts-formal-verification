import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.Common.if_4307119837691313886_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_4307119837691313886 (s₀ s₉ : State) : Prop := if_4307119837691313886_concrete_of_code.1 s₀ s₉

lemma if_4307119837691313886_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4307119837691313886_concrete_of_code s₀ s₉ →
  Spec A_if_4307119837691313886 s₀ s₉ := by
  intro h
  simpa [A_if_4307119837691313886] using h

end

end L2AssetRouter.Common
