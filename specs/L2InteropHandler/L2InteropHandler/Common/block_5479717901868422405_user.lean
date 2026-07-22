import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.mcopy

import generated.L2InteropHandler.L2InteropHandler.Common.block_5479717901868422405_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_block_5479717901868422405 (s₀ s₉ : State) : Prop := sorry

lemma block_5479717901868422405_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5479717901868422405_concrete_of_code s₀ s₉ →
  Spec A_block_5479717901868422405 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common
