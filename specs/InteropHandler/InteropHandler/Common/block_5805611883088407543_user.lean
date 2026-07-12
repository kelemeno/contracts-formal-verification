import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.fun_formatEvmV1

import generated.InteropHandler.InteropHandler.Common.block_5805611883088407543_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_5805611883088407543 (s₀ s₉ : State) : Prop := sorry

lemma block_5805611883088407543_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5805611883088407543_concrete_of_code s₀ s₉ →
  Spec A_block_5805611883088407543 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
