import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.finalize_allocation_21285

import generated.InteropHandler.InteropHandler.Common.block_1455986667034892369_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_1455986667034892369 (s₀ s₉ : State) : Prop := sorry

lemma block_1455986667034892369_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1455986667034892369_concrete_of_code s₀ s₉ →
  Spec A_block_1455986667034892369 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
