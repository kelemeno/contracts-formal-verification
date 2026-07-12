import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.finalize_allocation_21324

import generated.InteropHandler.InteropHandler.Common.block_85155899022391193_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_85155899022391193 (s₀ s₉ : State) : Prop := sorry

lemma block_85155899022391193_abs_of_concrete {s₀ s₉ : State} :
  Spec block_85155899022391193_concrete_of_code s₀ s₉ →
  Spec A_block_85155899022391193 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
