import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.array_allocation_size_bytes

import generated.L2InteropHandler.L2InteropHandler.Common.block_8890318276685480553_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_block_8890318276685480553 (s₀ s₉ : State) : Prop := block_8890318276685480553_concrete_of_code.1 s₀ s₉

lemma block_8890318276685480553_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8890318276685480553_concrete_of_code s₀ s₉ →
  Spec A_block_8890318276685480553 s₀ s₉ := by
  intro h
  simpa [A_block_8890318276685480553] using h

end

end L2InteropHandler.Common
