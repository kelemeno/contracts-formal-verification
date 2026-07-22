import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.finalize_allocation_22020

import generated.L2InteropHandler.L2InteropHandler.Common.block_1472197554759313605_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_block_1472197554759313605 (s₀ s₉ : State) : Prop := sorry

lemma block_1472197554759313605_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1472197554759313605_concrete_of_code s₀ s₉ →
  Spec A_block_1472197554759313605 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common
