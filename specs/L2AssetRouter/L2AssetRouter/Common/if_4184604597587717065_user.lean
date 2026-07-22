import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.panic_error_0x32

import generated.L2AssetRouter.L2AssetRouter.Common.if_4184604597587717065_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_if_4184604597587717065 (s₀ s₉ : State) : Prop := sorry

lemma if_4184604597587717065_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4184604597587717065_concrete_of_code s₀ s₉ →
  Spec A_if_4184604597587717065 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
