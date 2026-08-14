import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.checked_sub_uint256
import generated.InteropHandler.InteropHandler.array_allocation_size_bytes
import generated.InteropHandler.InteropHandler.finalize_allocation

import generated.InteropHandler.InteropHandler.Common.block_181012933440567358_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_181012933440567358 (s₀ s₉ : State) : Prop :=
  block_181012933440567358_concrete_of_code.1 s₀ s₉
lemma block_181012933440567358_abs_of_concrete {s₀ s₉ : State} :
  Spec block_181012933440567358_concrete_of_code s₀ s₉ →
  Spec A_block_181012933440567358 s₀ s₉ := by
  intro h
  simpa [A_block_181012933440567358] using h

end

end InteropHandler.Common
