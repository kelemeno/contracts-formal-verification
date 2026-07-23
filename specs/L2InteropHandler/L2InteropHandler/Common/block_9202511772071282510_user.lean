import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.array_allocation_size_array_bytes32_dyn
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation

import generated.L2InteropHandler.L2InteropHandler.Common.block_9202511772071282510_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_block_9202511772071282510 (s₀ s₉ : State) : Prop := block_9202511772071282510_concrete_of_code.1 s₀ s₉

lemma block_9202511772071282510_abs_of_concrete {s₀ s₉ : State} :
  Spec block_9202511772071282510_concrete_of_code s₀ s₉ →
  Spec A_block_9202511772071282510 s₀ s₉ := by
  intro h
  simpa [A_block_9202511772071282510] using h

end

end L2InteropHandler.Common
