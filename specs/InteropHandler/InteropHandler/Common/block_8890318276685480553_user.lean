import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.array_allocation_size_bytes

import generated.InteropHandler.InteropHandler.Common.block_8890318276685480553_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_8890318276685480553 (s₀ s₉ : State) : Prop := sorry

lemma block_8890318276685480553_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8890318276685480553_concrete_of_code s₀ s₉ →
  Spec A_block_8890318276685480553 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
