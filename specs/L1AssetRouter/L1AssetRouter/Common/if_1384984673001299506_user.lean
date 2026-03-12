import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_1384984673001299506_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_1384984673001299506 (s₀ s₉ : State) : Prop :=
  if_1384984673001299506_concrete_of_code.1 s₀ s₉

lemma if_1384984673001299506_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1384984673001299506_concrete_of_code s₀ s₉ →
  Spec A_if_1384984673001299506 s₀ s₉ := by
  intro h
  simpa [A_if_1384984673001299506] using h

end

end L1AssetRouter.Common
