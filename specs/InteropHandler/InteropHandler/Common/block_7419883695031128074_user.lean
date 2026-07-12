import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.fun_slice

import generated.InteropHandler.InteropHandler.Common.block_7419883695031128074_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_7419883695031128074 (s₀ s₉ : State) : Prop := sorry

lemma block_7419883695031128074_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7419883695031128074_concrete_of_code s₀ s₉ →
  Spec A_block_7419883695031128074 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
