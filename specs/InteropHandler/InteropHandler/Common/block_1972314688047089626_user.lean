import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.mcopy

import generated.InteropHandler.InteropHandler.Common.block_1972314688047089626_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_1972314688047089626 (s₀ s₉ : State) : Prop := sorry

lemma block_1972314688047089626_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1972314688047089626_concrete_of_code s₀ s₉ →
  Spec A_block_1972314688047089626 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
