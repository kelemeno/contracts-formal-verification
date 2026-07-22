import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.panic_error_0x41

import generated.L2AssetRouter.L2AssetRouter.Common.if_4148053531410514966_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_if_4148053531410514966 (s₀ s₉ : State) : Prop := sorry

lemma if_4148053531410514966_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4148053531410514966_concrete_of_code s₀ s₉ →
  Spec A_if_4148053531410514966 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
