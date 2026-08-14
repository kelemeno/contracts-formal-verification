import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.mcopy

import generated.InteropHandler.InteropHandler.Common.block_2935294839909559400_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_2935294839909559400 (s₀ s₉ : State) : Prop :=
  block_2935294839909559400_concrete_of_code.1 s₀ s₉
lemma block_2935294839909559400_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2935294839909559400_concrete_of_code s₀ s₉ →
  Spec A_block_2935294839909559400 s₀ s₉ := by
  intro h
  simpa [A_block_2935294839909559400] using h

end

end InteropHandler.Common
