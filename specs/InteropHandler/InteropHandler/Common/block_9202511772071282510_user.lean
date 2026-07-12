import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.array_allocation_size_array_bytes32_dyn
import generated.InteropHandler.InteropHandler.finalize_allocation

import generated.InteropHandler.InteropHandler.Common.block_9202511772071282510_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_9202511772071282510 (s₀ s₉ : State) : Prop := sorry

lemma block_9202511772071282510_abs_of_concrete {s₀ s₉ : State} :
  Spec block_9202511772071282510_concrete_of_code s₀ s₉ →
  Spec A_block_9202511772071282510 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
