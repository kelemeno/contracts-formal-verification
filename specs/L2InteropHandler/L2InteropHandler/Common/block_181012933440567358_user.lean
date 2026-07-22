import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.checked_sub_uint256
import generated.L2InteropHandler.L2InteropHandler.array_allocation_size_bytes
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation

import generated.L2InteropHandler.L2InteropHandler.Common.block_181012933440567358_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_block_181012933440567358 (s₀ s₉ : State) : Prop := sorry

lemma block_181012933440567358_abs_of_concrete {s₀ s₉ : State} :
  Spec block_181012933440567358_concrete_of_code s₀ s₉ →
  Spec A_block_181012933440567358 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common
